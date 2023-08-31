use contiguous_mem::prelude::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Data {
    value: u32,
}

fn main() {
    // Create a ContiguousMemory instance with a capacity of 1024 bytes and 1-byte alignment
    let mut memory = UnsafeContiguousMemory::new(1024);

    // Store data in the memory container
    let data = Data { value: 42 };

    let stored_number: *mut u64 = memory
        .store(22u64)
        .expect("there should be enough space to store a number");
    let stored_data: *mut Data = memory
        .store(data)
        .expect("there should be enough space to store Data");

    // Retrieve and use the stored data
    unsafe {
        assert_eq!(*stored_data, data);
        assert_eq!(*stored_number, 22);
    }
}
