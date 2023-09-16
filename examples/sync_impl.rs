use contiguous_mem::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Data {
    value: u32,
}

fn main() {
    let storage = SyncContiguousMemory::new(4096);

    let mut sent_storage = storage.clone();
    let writer_one =
        std::thread::spawn(move || sent_storage.push(22u64).expect("unable to store number"));

    let data = Data { value: 42 };

    let mut sent_storage = storage.clone();
    let writer_two = std::thread::spawn(move || {
        sent_storage
            .push(Data { value: 42 })
            .expect("unable to store Data")
    });

    let stored_number: SyncContiguousEntryRef<u64> =
        writer_one.join().expect("unable to join number thread");
    let mut stored_number_clone = stored_number.clone();
    let stored_data: SyncContiguousEntryRef<Data> =
        writer_two.join().expect("unable to join Data thread");

    let number_ref = stored_number
        .get()
        .expect("number ref poisoned on first use");
    let stored_data = stored_data.get().expect("Data ref poisoned on first use");

    // note that number is still locked here
    assert!(
        stored_number_clone.try_get_mut().is_err(),
        "number reference should not be writable as the number is currently borrowed"
    );

    assert_eq!(*number_ref, 22);
    assert_eq!(*stored_data, data);
}
