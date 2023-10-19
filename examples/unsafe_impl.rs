use contiguous_mem::{types::ImplUnsafe, *};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Data {
    value: u32,
}

fn main() {
    // Create a ContiguousMemory instance with a capacity of 1024 bytes and 1-byte alignment
    let mut memory = ContiguousMemory::<ImplUnsafe>::with_capacity(1024);

    // Store data in the memory container
    let data = Data { value: 42 };

    let stored_number: *mut u64 = memory.push(22u64);
    let stored_data: *mut Data = memory.push(data);

    // Retrieve and use the stored data
    unsafe {
        assert!(!stored_data.is_null());
        assert_eq!(*stored_data, data);
        assert!(!stored_number.is_null());
        assert_eq!(*stored_number, 22);
    }
}
