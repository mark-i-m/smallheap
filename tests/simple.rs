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
