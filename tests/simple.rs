extern crate smallheap;

use smallheap::KernelHeap;

#[test]
fn test_init_dumbest_possible() {
    const SIZE: usize = 1 << 12;
    let mut mem = [0u8; SIZE];

    let h = unsafe { KernelHeap::new(mem.as_mut_ptr(), SIZE) };

    assert_eq!(h.size(), SIZE);
    assert_eq!(h.free_bytes(), h.size());
}

#[test]
fn test_simple_alloc_free() {
    const SIZE: usize = 1 << 12;
    let mut mem = [0u8; SIZE];

    let mut h = unsafe { KernelHeap::new(mem.as_mut_ptr(), SIZE) };

    assert_eq!(h.free_bytes(), h.size());

    let x = unsafe { h.malloc(SIZE, 0) };

    assert_eq!(x, mem.as_mut_ptr());
    assert_eq!(h.free_bytes(), 0);

    unsafe {
        h.free(x, SIZE);
    }

    assert_eq!(h.free_bytes(), h.size());
}
