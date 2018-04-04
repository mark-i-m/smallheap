//! This file contains the memory allocator used by the kernel.
//!
//! The implementation in this file is a simple first-fit allocator. Most of the code is not
//! thread-safe, but the `KernelAllocator` type which implements `Alloc` is.
//!
//! Invariants:
//! * BLOCK_ALIGN = 4*size_of::<usize>()
//! * All blocks will be a multiple of BLOCK_ALIGN
//! * All blocks will be BLOCK_ALIGN-aligned
//!
//! Block structure:
//! * size
//! * forward pointer | free bits
//! * backward pointer | 0x0
//!   ...
//! * size (last word)
//!
//! When a block is free, the first and last words should match and be equal to the size of the
//! block. The forward pointer points to the head of the next free block. The backward pointer
//! points to the head of the previous free block. Since all blocks are at least 16B aligned, at
//! least the last 4 bits of all block addresses are 0. The last 4 bits of the forward pointer
//! should be all 1s if the block is free.
//!
//! When a block is in use, the whole block is usable for the user. Thus, usable size and block
//! size are equal.

extern crate core;

use core::{ptr, slice, mem::{self, size_of}};

// A couple of constants

/// A flag to turn on and off debugging output
#[cfg(feature = "debug")]
const DEBUG: bool = true;

/// A flag to turn on and off debugging output
#[cfg(not(feature = "debug"))]
const DEBUG: bool = false;

/// A const representing the minimum alignment of any block. Should be a power of two.
const BLOCK_ALIGN: usize = 4 * size_of::<usize>();

// A couple of utilities

/// Round up to the nearest multiple of `BLOCK_ALIGN`
fn round_to_block_align(size: usize) -> usize {
    round_to_n(size, BLOCK_ALIGN)
}

/// Round the size to `n`. `n` must be a power of 2
fn round_to_n(size: usize, n: usize) -> usize {
    if size % n == 0 {
        size
    } else {
        size - (size % n) + n
    }
}

// The kernel allocator implementation...

/// The heap implementation itself.
pub struct KernelHeap {
    /// The start address of the kernel heap
    start: usize,

    /// The end address of the kernel heap. That is, the first address that is not in the heap.
    end: usize,

    /// The first block of the heap
    free_list: Option<Block>,

    /// The number of free bytes in the heap
    free_bytes: usize,

    // heap stats
    /// The number of successful mallocs (for stats purposes)
    success_mallocs: usize,

    /// The number of unsuccessful mallocs (for stats purposes)
    fail_mallocs: usize,

    /// The number of successful frees (for stats purposes)
    frees: usize,
}

impl KernelHeap {
    /// Create a new heap starting at address `start` with the given `size` in bytes.
    pub unsafe fn new(start: *mut u8, size: usize) -> Self {
        #[cfg(feature = "debug")]
        println!("heap::new({:p}, {})", start, size);

        // Block align the beginning
        let original_start = start as usize;
        let start = round_to_block_align(original_start);

        // round end down
        let end = (original_start + size) & !(BLOCK_ALIGN - 1);

        // bounds check
        if end <= start {
            panic!("No heap space");
        }

        // create first block and free list
        let mut first = Block::from_raw_parts(start as *mut u8, end - start);
        first.set_size(end - start);
        first.mark_free();
        first.set_next(None);
        first.set_prev(None);

        #[cfg(feature = "debug")]
        println!(
            "heap inited - start addr: 0x{:x}, end addr: 0x{:x}, {} bytes\n",
            start,
            end,
            end - start
        );

        KernelHeap {
            start,
            end,
            free_list: Some(first),
            free_bytes: end - start,
            success_mallocs: 0,
            fail_mallocs: 0,
            frees: 0,
        }
    }

    /// Return a pointer to `size` bytes of memory aligned to `align`.
    ///
    /// On failure, return a null pointer.
    ///
    /// Behavior is undefined if the requested size is 0 or the alignment is not a
    /// power of 2. The alignment must be no larger than the largest supported page
    /// size on the platform.
    pub unsafe fn malloc(&mut self, size: usize, align: usize) -> *mut u8 {
        if DEBUG {
            #[cfg(feature = "debug")]
            println!("malloc {}, {} -> ", size, align);
        }

        if size == 0 {
            return 0 as *mut u8;
        }

        let size = round_to_block_align(size);
        let align = align.next_power_of_two();

        // get a free block
        let (mut begin, split_size) = if let Some(block) = self.find_block(size, align) {
            block
        } else {
            if self.free_list.is_none() {
                panic!("Out of memory!");
            } else {
                // NOTE: fail for now because rustc does not know how to handle failed mallocs
                // TODO: is this still true?
                panic!(
                    "malloc({}, {}) -> *** malloc failed, rustc cannot handle this :( ***\n",
                    size, align
                );
            }

            // update stats
            // self.fail_mallocs += 1;

            // return 0 as *mut u8;
        };

        // split block if needed
        if split_size > 0 {
            // split off the first half and leave it. We want the second half.
            let second = begin.split(split_size);
            begin.insert(&mut self.free_list);
            begin = second;
        }

        // split block to fit and insert the remainder back into the free list
        if begin.get_size() > size {
            let newblk = begin.split(size);
            newblk.insert(&mut self.free_list);
        }

        // update heap metadata
        self.free_bytes -= begin.get_size();

        // make block used
        begin.mark_used();

        // mess up metadata so as to make life easier later
        begin.set_foot(0xFFFFFFFF);
        begin.set_head(0xFFFFFFFF);

        // update stats
        self.success_mallocs += 1;

        if DEBUG {
            #[cfg(feature = "debug")]
            println!("0x{:p}\n", begin.as_mut_ptr());
        }

        begin.as_mut_ptr()
    }

    /// Deallocates the memory referenced by `ptr`.
    ///
    /// The `ptr` parameter must not be null.
    ///
    /// The `old_size` and `align` parameters are the parameters that were used to
    /// create the allocation referenced by `ptr`. The `old_size` parameter may be
    /// any value in range_inclusive(requested_size, usable_size).
    pub unsafe fn free(&mut self, ptr: *mut u8, old_size: usize) {
        if DEBUG {
            #[cfg(feature = "debug")]
            println!("free 0x{:p}, {}\n", ptr, old_size);
        }

        // check input
        if ptr == ptr::null_mut() {
            panic!("Attempt to free NULL ptr");
        }

        // get actual size of block
        let old_size = round_to_block_align(old_size);

        let mut block = Block::from_raw_parts(ptr, old_size);

        // update heap metadata
        self.free_bytes += block.get_size();

        // sanity
        if block.is_free() {
            panic!("Double free: {:p}", ptr);
        }

        // Create block and insert into free list
        block.set_size(old_size);
        block.mark_free();
        block.set_next(None);
        block.set_prev(None);
        block.insert(&mut self.free_list);

        // update stats
        self.frees += 1;
    }

    /// Return the number of bytes of this heap.
    pub fn size(&self) -> usize {
        self.end - self.start
    }

    /// Return the number of free bytes of this heap.
    pub fn free_bytes(&self) -> usize {
        self.free_bytes
    }

    /// Find a block with the right size and alignment. Remove the block from the free list and
    /// return it along with where to split it. Or return None if no block is found.
    fn find_block(&mut self, size: usize, align: usize) -> Option<(Block, usize)> {
        // the list head is a bit special because it "owns" the rest of the list...
        let mut blk =
            if let Some(mut begin) = self.free_list.as_ref().map(|b| unsafe { b.clone_unsafe() }) {
                // is the first node what we need?
                if let Some(split_size) = begin.is_match(size, align) {
                    begin.remove(&mut self.free_list);
                    return Some((begin, split_size));
                }

                begin.get_free_next()
            } else {
                // list is empty!
                return self.oom(size, align);
            };

        // if the beginning of the list didn't suit our needs, then look at the rest of the list
        while let Some(mut blk_) = blk {
            // is this block the right size/align?
            if let Some(split_size) = blk_.is_match(size, align) {
                blk_.remove(&mut self.free_list);
                return Some((blk_, split_size));
            }

            blk = blk_.get_free_next();
        }

        // no blocks found
        return self.oom(size, align);
    }

    /// Handle an out of memory situation. Attempts to coalesce blocks. Then retry an allocation
    /// and return any block that is found. Otherwise, return None.
    fn oom(&mut self, _size: usize, _align: usize) -> Option<(Block, usize)> {
        // TODO: fix me
        // attempt coalescing
        //let next_block = (*block).get_contiguous_next();
        //if (*next_block).is_free() {
        //    (*block).merge_with_next();
        //}

        // TODO: fix me
        // let prev_block = (*block).get_contiguous_prev();
        // if !prev_block.is_null() && (*prev_block).is_free() {
        //    (*prev_block).merge_with_next();
        // }
        None
    }

    // Useful for debugging

    /// Prints implementation-defined allocator statistics.
    ///
    /// These statistics may be inconsistent if other threads use the allocator during the call.
    #[cfg(feature = "debug")]
    fn print_stats(&self) {
        unsafe {
            println!("\nHeap stats\n----------\n");

            // Number of free blocks and amount of free memory
            let (num_free, size_free, size_used) = self.get_block_stats();
            println!(
                "{} free blocks; {} bytes free, {} bytes used\n",
                num_free, size_free, size_used
            );

            // Number of mallocs and frees
            println!(
                "Successfull mallocs: {}; Failed mallocs: {}; Frees: {}\n\n",
                self.success_mallocs, self.fail_mallocs, self.frees
            );
        }
    }

    /// Helper method to compute stats
    #[cfg(feature = "debug")]
    fn get_block_stats(&self) -> (usize, usize, usize) {
        // counters
        let mut num_free = 0;
        let mut size_free = 0;

        // the list head is a bit special because it "owns" the rest of the list...
        let mut blk = self.free_list.as_ref().map(|b| unsafe { b.clone_unsafe() });

        // if the beginning of the list didn't suit our needs, then look at the rest of the list
        while let Some(mut blk_) = blk {
            num_free += 1;
            size_free += blk_.get_size();
            println!("free {:p}: {} B\n", blk_.as_mut_ptr(), blk_.get_size());
            blk = blk_.get_free_next();
        }

        (num_free, size_free, self.end - self.start - size_free)
    }
}

/// A single heap block
struct Block {
    data: &'static mut [u32],
}

impl Block {
    /// Construct a `Block` from a pointer to the beginning and the length in bytes.
    pub unsafe fn from_raw_parts(ptr: *mut u8, len: usize) -> Self {
        Block {
            data: slice::from_raw_parts_mut(ptr as *mut u32, len),
        }
    }

    pub unsafe fn clone_unsafe(&self) -> Self {
        Block {
            data: slice::from_raw_parts_mut(self.as_ptr() as *mut u32, self.data.len()),
        }
    }

    /// Returns a raw pointer to the beginning of the block
    pub fn as_ptr(&self) -> *const u8 {
        self.data.as_ptr() as *const u8
    }

    /// Returns a raw pointer to the beginning of the block
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.data.as_mut_ptr() as *mut u8
    }

    /// Return the contents of the first word of the block given a pointer to the first word.
    unsafe fn get_head_raw(ptr: *const u8) -> usize {
        *(ptr as *const usize)
    }

    /// Returns the first word of the block, which will contain the size if this is a free block
    fn get_head(&self) -> usize {
        self.data[0] as usize
    }

    /// Sets the header to the given value
    fn set_head(&mut self, head: usize) {
        self.data[0] = head as u32;
    }

    /// Returns the last word of the block, which will contain the size if this is a free block
    fn get_foot(&self) -> usize {
        *self.data.last().unwrap() as usize
    }

    /// Sets the footer to the given value
    fn set_foot(&mut self, foot: usize) {
        *self.data.last_mut().unwrap() = foot as u32;
    }

    /// Gets the 4 free bits of the block
    fn get_free_bits(&self) -> u8 {
        (self.data[1] & 0xF) as u8
    }

    /// Set the forward pointer (but not the free bits)
    pub fn set_next(&mut self, next: Option<&Block>) {
        let free_bits = self.get_free_bits() as u32;
        self.data[1] = if let Some(next) = next {
            ((next.as_ptr() as u32) & !0xF) | free_bits
        } else {
            free_bits
        };
    }

    /// Set the backward pointer
    pub fn set_prev(&mut self, prev: Option<&Block>) {
        self.data[2] = if let Some(prev) = prev {
            (prev.as_ptr() as u32) & !0xF
        } else {
            0
        };
    }

    /// Returns true if the block is a valid free block. This method does a lot of sanity
    /// checking.
    ///
    /// It doesn't really make sense to ask this. The only way to know a block is free is to
    /// find it in the free list. However, this is useful for sanity checking and debugging.
    pub fn is_free(&self) -> bool {
        // make sure the block addr is reasonable
        //let self_usize = self.as_mut_ptr() as usize;
        //if self_usize < self.start || self_usize >= self.end || self_usize % BLOCK_ALIGN != 0 {
        //    return false;
        //}

        let head = self.get_head();

        // make sure the block size is reasonable
        //if head < BLOCK_ALIGN || head % BLOCK_ALIGN != 0 || head > self.end - self.start {
        //    return false;
        //}

        let foot = self.get_foot();

        // check sentinels
        if head != foot {
            panic!("Sentinels don't match! {:x} {:x}", head, foot);
        }

        // check that free list pointers are valid
        //let forward_ptr = self.get_free_next();
        //let backward_ptr = self.get_free_prev();

        //if (forward_ptr.is_some() && forward_ptr.unwrap().as_mut_ptr() < (self.start as *mut u8))
        //    || (forward_ptr.is_some() && forward_ptr.unwrap().as_mut_ptr() >= (self.end as *mut u8))
        //    || (backward_ptr.is_some()
        //        && backward_ptr.unwrap().as_mut_ptr() < (self.start as *mut u8))
        //    || (backward_ptr.is_some()
        //        && backward_ptr.unwrap().as_mut_ptr() >= (self.end as *mut u8))
        //{
        //    return false;
        //}

        // check that the block is free
        self.get_free_bits() == 0xF
    }

    /// Set the free bits
    pub fn mark_free(&mut self) {
        self.data[1] |= 0xF;
    }

    /// Clear the free bits. The block should already be removed from the free list
    pub fn mark_used(&mut self) {
        self.data[1] &= !0xF;
    }

    /// Return the contents of the first word of the block given a pointer to the first word.
    unsafe fn get_size_raw(ptr: *const u8) -> usize {
        Block::get_head_raw(ptr)
    }

    /// Return the size of the block (user-usable data size)
    pub fn get_size(&self) -> usize {
        self.get_head()
    }

    /// Set the size of block
    pub fn set_size(&mut self, size: usize) {
        self.set_head(size);
        self.set_foot(size);
    }

    /// Returns the heap block immediately following this one. If there is no next block or the
    /// nextnext block is not free, then this is undefined behavior...
    pub unsafe fn get_contiguous_next(&self) -> Block {
        let ptr = self.as_ptr();
        let size = self.get_size();

        // avoid overflows and weirdness
        //if size >= self.end - self.start {
        //    panic!("Huge block at {:x}\n", ptr as usize);
        //}

        // Pointer to the beginning of the next block
        let ptr = ptr.offset(size as isize);
        let len = Block::get_size_raw(ptr);

        Block::from_raw_parts(ptr as *mut u8, len)
    }

    /// Returns the heap block immediately preceding this one. If there is no previous block or the
    /// previous block is not free, then this is undefined behavior...
    pub unsafe fn get_contiguous_prev(&self) -> Block {
        let prev_size_ptr = (self.as_ptr() as *const usize).offset(-1);

        // sanity: check that we are still in the heap
        //if (prev_size_ptr as usize) < self.start {
        //    panic!("Block before the beginning of the heap!");
        //}

        let prev_size = *prev_size_ptr;

        // sanity: check that the size is reasonable
        //if prev_size >= self.end - self.start || prev_size == 0 {
        //    panic!("Unreasonable heap block size: {} bytes", prev_size);
        //}

        // get pointer to previous block
        let ptr = self.as_ptr().offset(-(prev_size as isize));

        Block::from_raw_parts(ptr as *mut u8, prev_size)
    }

    /// Returns the next `Block` in the free list if there is one.
    pub fn get_free_next(&self) -> Option<Block> {
        let next_ptr = (self.data[1] & !0xF) as *mut u8;

        if next_ptr.is_null() {
            None
        } else {
            unsafe {
                let next_size = Block::get_size_raw(next_ptr);
                Some(Block::from_raw_parts(next_ptr, next_size))
            }
        }
    }

    /// Returns the previous `Block` in the free list if there is one.
    pub fn get_free_prev(&self) -> Option<Block> {
        let prev_ptr = (self.data[2] & !0xF) as *mut u8;

        if prev_ptr.is_null() {
            None
        } else {
            unsafe {
                let prev_size = Block::get_size_raw(prev_ptr);
                Some(Block::from_raw_parts(prev_ptr, prev_size))
            }
        }
    }

    /// Remove from free list. Clear forward/backward pointers.
    pub fn remove(&mut self, free_list: &mut Option<Block>) {
        // sanity: make sure the block is free and valid
        if !self.is_free() {
            panic!(
                "Attempt to remove used block from free list: {:p}\n",
                self.as_mut_ptr()
            );
        }

        // swap pointers
        let mut next = self.get_free_next();
        let mut prev = self.get_free_prev();

        if let Some(ref mut next) = next {
            next.set_prev(prev.as_ref());
        }

        if let Some(ref mut prev) = prev {
            prev.set_next(next.as_ref());
        } else {
            *free_list = next;
        }

        self.set_next(None);
        self.set_prev(None);
    }

    /// Add to head of free list
    pub fn insert(mut self, free_list: &mut Option<Block>) {
        let old_head = free_list.take();

        if !self.is_free() {
            panic!("Adding taken block to free list: {:p}", self.as_mut_ptr());
        }

        self.set_next(old_head.as_ref());
        self.set_prev(None);

        if let Some(mut old_head) = old_head {
            old_head.set_prev(Some(&self));
        }

        *free_list = Some(self);
    }

    /// Merge this block with the next block.  Removes the second block from the free list before
    /// merging. If the next block is not free, this is undefined behavior.
    pub unsafe fn merge_with_next(&mut self, free_list: &mut Option<Block>) {
        // make sure both blocks are free and valid
        if !self.is_free() {
            panic!(
                "Attempt to merge non-free block {:p} with next",
                self.as_mut_ptr()
            );
        }

        let mut next = self.get_contiguous_next();
        if !next.is_free() {
            panic!(
                "Attempt to merge {:p} with non-free block {:p}",
                self.as_mut_ptr(),
                next.as_mut_ptr()
            );
        }

        // remove next block from free list
        next.remove(free_list);

        // Extend the block
        let new_size = self.get_size() + next.get_size();
        let new_data = slice::from_raw_parts_mut(self.as_mut_ptr() as *mut u32, new_size);
        let old_data = mem::replace(&mut self.data, new_data);
        mem::forget(old_data);
        self.set_size(new_size);
    }

    /// Split the block so that it is the given size. Return the newly created block (the end
    /// portion of the old block). The block must be large enough to split (`>= 2*BLOCK_ALIGN`).
    /// The block must be free, but not necessarily in the free list. The new size must be a
    /// multiple of `BLOCK_ALIGN`.
    pub fn split(&mut self, size: usize) -> Block {
        // make sure the block is free and valid
        if !self.is_free() {
            panic!(
                "Attempt to split non-free block: {:x}",
                self as *const Block as usize
            );
        }

        let old_size = self.get_size();

        // make sure the block is large enough
        if old_size < 32 {
            panic!(
                "Block is to small to split: {:x}",
                self as *const Block as usize
            );
        }

        if old_size < size + BLOCK_ALIGN {
            panic!(
                "Block is to small to split at {}: {:x}",
                size, self as *const Block as usize
            );
        }

        let new_block_size = old_size - size;

        // make this block smaller
        let new_data = unsafe { slice::from_raw_parts_mut(self.as_mut_ptr() as *mut u32, size) };
        let old_data = mem::replace(&mut self.data, new_data);
        mem::forget(old_data);
        self.set_size(size);

        // create the new block
        let new_block_ptr = unsafe { self.as_mut_ptr().offset(size as isize) };
        let mut new_block = unsafe { Block::from_raw_parts(new_block_ptr, new_block_size) };

        new_block.set_size(new_block_size);
        new_block.mark_free();
        new_block.set_next(None);
        new_block.set_prev(None);

        new_block
    }

    /// Returns `Some(size)` if this block matches the requested size and alignment.  The returned
    /// size is the size at which the block should be split to obtain an aligned block; otherwise,
    /// returns `None`.
    pub fn is_match(&self, size: usize, align: usize) -> Option<usize> {
        let block_addr = self.as_ptr() as usize;
        let aligned = round_to_n(block_addr, align);

        // aligned part needs to be at least size bytes
        let split_size = aligned - block_addr;

        if self.get_size() >= size + split_size {
            Some(split_size)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::mem;

    #[derive(Clone, Copy)]
    #[cfg_attr(target_pointer_width = "64", repr(align(32)))]
    #[cfg_attr(target_pointer_width = "32", repr(align(16)))]
    struct BlockAligned([usize; 4]);

    macro_rules! new_block_aligned {
        ($size:expr) => {
            [BlockAligned([0; 4]); $size / BLOCK_ALIGN]
        }
    }

    #[test]
    fn test_block_align() {
        assert!(BLOCK_ALIGN.is_power_of_two());
    }

    #[test]
    fn test_init_aligned() {
        const SIZE: usize = 1 << 12;
        let mut mem = new_block_aligned!(SIZE);

        assert_eq!(SIZE, mem.len() * mem::size_of::<BlockAligned>());

        let h = unsafe { KernelHeap::new(mem.as_mut_ptr() as *mut u8, SIZE) };

        // make sure we don't consume more space than we are given
        assert!(h.start >= (mem.as_mut_ptr() as usize));
        assert!(h.end <= unsafe { (mem.as_mut_ptr().offset(SIZE as isize) as usize) });

        // make sure we are not wasting too much space
        assert_eq!(h.size(), SIZE);
        assert_eq!(h.free_bytes(), h.size());
    }

    #[test]
    fn test_init_not_aligned() {
        unimplemented!();
    }
}
