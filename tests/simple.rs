extern crate smallheap;

use std::collections::HashSet;

use smallheap::Allocator;

#[test]
fn test_simple_alloc_free() {
    const SIZE: usize = 1 << 12;
    let mut mem = [0u8; SIZE];

    let mut h = unsafe { Allocator::new(mem.as_mut_ptr(), SIZE) };
    let max = h.size();

    assert_eq!(h.free_bytes(), h.size());

    let x = unsafe { h.malloc(max, 0) };

    assert_eq!(h.free_bytes(), 0);

    unsafe {
        h.free(x, max);
    }

    assert_eq!(h.free_bytes(), h.size());
}

#[test]
fn test_simple_alloc_free_alot() {
    const SIZE: usize = 1 << 12;
    let mut mem = [0u8; SIZE];

    let mut h = unsafe { Allocator::new(mem.as_mut_ptr(), SIZE) };

    assert_eq!(h.free_bytes(), h.size());

    for _ in 0..10000 {
        let x = unsafe { h.malloc(32, 0) };
        unsafe {
            h.free(x, 32);
        }
    }

    assert_eq!(h.free_bytes(), h.size());
}

#[test]
fn test_mem_leak_safe() {
    const SIZE: usize = 1 << 12;
    let mut mem = [0u8; SIZE];

    let mut h = unsafe { Allocator::new(mem.as_mut_ptr(), SIZE) };

    assert_eq!(h.free_bytes(), h.size());

    // we should be able to just do a bunch of mallocs safely
    for i in 0..120 {
        let x = unsafe { h.malloc(32, 0) };
        assert!(!x.is_null());
        assert!(x >= mem.as_mut_ptr());
        assert!(x < unsafe { mem.as_mut_ptr().offset(SIZE as isize) });
        assert_eq!(h.free_bytes(), h.size() - (i + 1) * 32);
    }
}

#[test]
fn test_pattern_out_of_bounds() {
    const SIZE: usize = 1 << 12;
    let mut mem = [0u8; SIZE * 2];

    let mut h = unsafe { Allocator::new(mem[SIZE / 2..].as_mut_ptr(), SIZE) };

    assert_eq!(h.free_bytes(), h.size());

    let mut ptrs = HashSet::new();

    for _ in 0..120 {
        let x = unsafe { h.malloc(32, 0) };
        ptrs.insert(x);
    }

    for x in ptrs.drain() {
        unsafe {
            h.free(x, 32);
        }
    }

    assert_eq!(h.free_bytes(), h.size());

    // make sure we don't touch any bytes outside the heap
    assert!(mem[0..SIZE / 2].iter().all(|x| x == &0));
    assert!(mem[SIZE + SIZE / 2..].iter().all(|x| x == &0));
}

#[test]
fn test_simple_alloc_free_simple_pattern() {
    const SIZE: usize = 1 << 12;
    let mut mem = [0u8; SIZE];

    let mut h = unsafe { Allocator::new(mem.as_mut_ptr(), SIZE) };

    assert_eq!(h.free_bytes(), h.size());

    let mut ptrs = HashSet::new();

    for _ in 0..120 {
        let x = unsafe { h.malloc(32, 0) };
        ptrs.insert(x);
    }

    for x in ptrs.drain() {
        unsafe {
            h.free(x, 32);
        }
    }

    assert_eq!(h.free_bytes(), h.size());
}
