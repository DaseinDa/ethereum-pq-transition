//! The heap that one verification asks for, counted by an allocator that wraps the system's.
//!
//! The program's heap is 32 KiB and is never freed, so every request counts in full, whether or not the
//! memory is given back.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

use fips204::ml_dsa_44;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _};
use pq_verify_in_vm::mldsa44;

thread_local! {
    static COUNTING: Cell<bool> = const { Cell::new(false) };
    static REQUESTS: Cell<usize> = const { Cell::new(0) };
    static BYTES: Cell<usize> = const { Cell::new(0) };
}

fn count(bytes: usize) {
    if COUNTING.with(Cell::get) {
        REQUESTS.with(|requests| requests.set(requests.get() + 1));
        BYTES.with(|total| total.set(total.get() + bytes));
    }
}

struct CountingAllocator;

// The only unsafe code of the crate's own sources: a test allocator that forwards every call to the system
// allocator unchanged.
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        count(layout.size());
        System.alloc(layout)
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        count(layout.size());
        System.alloc_zeroed(layout)
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        count(new_size);
        System.realloc(ptr, layout, new_size)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

/// Requests and bytes that `run` asks the allocator for on this thread.
fn measure<T>(run: impl FnOnce() -> T) -> (T, usize, usize) {
    REQUESTS.with(|requests| requests.set(0));
    BYTES.with(|total| total.set(0));
    COUNTING.with(|counting| counting.set(true));
    let result = run();
    COUNTING.with(|counting| counting.set(false));
    (result, REQUESTS.with(Cell::get), BYTES.with(Cell::get))
}

#[test]
fn verification_allocates_one_block_of_7168_bytes() {
    let (pk, sk) = ml_dsa_44::KG::keygen_from_seed(&[5; 32]);
    let pk = pk.into_bytes();
    let message = [b"pq-enroll-v1".as_slice(), &[6; 32], &pk].concat();
    let sig = sk.try_sign_with_seed(&[7; 32], &message, &[]).expect("signing");

    // A valid signature runs the whole verification.
    let (valid, requests, bytes) = measure(|| mldsa44::verify(&pk, &message, &sig));
    assert!(valid);
    assert_eq!((requests, bytes), (1, 7168));

    // A signature that fails the last comparison costs the same.
    let mut tampered = sig;
    tampered[100] ^= 1;
    let (valid, requests, bytes) = measure(|| mldsa44::verify(&pk, &message, &tampered));
    assert!(!valid);
    assert_eq!((requests, bytes), (1, 7168));

    // A malformed hint is refused before any memory is requested.
    let mut malformed = sig;
    malformed[mldsa44::SIGNATURE_LEN - 1] = 81;
    let (valid, requests, bytes) = measure(|| mldsa44::verify(&pk, &message, &malformed));
    assert!(!valid);
    assert_eq!((requests, bytes), (0, 0));

    println!("heap: one verification makes 1 request of 7168 bytes (7 polynomials of 256 32-bit coefficients)");
}
