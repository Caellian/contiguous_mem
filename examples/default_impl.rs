use contiguous_mem::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Data {
    value: u32,
}

fn main() {
    // Create a ContiguousMemory instance with a capacity of 1024 bytes and 1-byte alignment
    let mut memory = ContiguousMemory::new(1024);

    // Store data in the memory container
    let data = Data { value: 42 };
    let stored_number: ContiguousEntryRef<u64> = memory.push(22u64);
    let stored_data: ContiguousEntryRef<Data> = memory.push(data);

    // Retrieve and use the stored data
    assert_eq!(*stored_data.get(), data);
    assert_eq!(*stored_number.get(), 22);
}
