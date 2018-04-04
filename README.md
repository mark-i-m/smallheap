# smallheap

A simple, lightweight, space-efficient heap allocator.

This is a straight-forward, no-frills allocator. It uses a first-fit policy.

NOTE: I haven't extensively tested this yet... feel free to file issues.

### Features

- O(1) space overhead. Really, it is at most a few dozen bytes. There is exactly 0 space
  overhead per allocation, though.
- `no_std` compatible. Use the `no_std` feature in your `Cargo.toml`.

### Caveats

- The allocator is not thread-safe. If you need thread-safety, you should wrap the heap in a
  `Mutex` or something.
- The allocator does not do too much to prevent fragmentation. This is OK if you expect to
  keep allocating and deallocating chunks of the same size. Allocation may try to coalesce
  previously freed blocks, but there is a configurable limit to how much it tries to do this
  so that we can guarantee bounded time for allocation. Freeing a block never coallesces.
- Only works on architectures with pointer widths >= 32 bits.
- Does no sanity checking on `free`'s arguments. The use is entirely responsible for passing
  the correct arguments to `free`. This is reasonably easy if you are using it as a global
  allocator because the compiler does that for you :)

### Usage

If you intend to use this as a global allocator, you can easily wrap this with `liballoc`'s
`heap::allocator` API. Otherwise, you can just instantiate a `smallheap::Allocator` singleton
object with some memory and use that.
