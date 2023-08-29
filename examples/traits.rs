use contiguous_mem::{vtable, ContiguousMemoryRef, GrowableContiguousMemory};

trait Greetable {
    fn print_hello(&self);
}

struct Person(String);
impl Greetable for Person {
    fn print_hello(&self) {
        println!("Saying hello to person: {}", self.0);
    }
}

struct Dog(String);
impl Greetable for Dog {
    fn print_hello(&self) {
        println!("Saying hello to dog: {}", self.0);
    }
}

fn main() {
    let mut storage = GrowableContiguousMemory::new(4096);

    let person1: ContiguousMemoryRef<dyn Greetable> = unsafe {
        storage
            .store(Person("Joe".to_string()))
            .expect("unable to store person1")
            .as_dyn(vtable!(Person as Greetable))
    };

    let person2 = storage
        .store(Person("Craig".to_string()))
        .expect("unable to store person2");

    let dog = storage
        .store(Dog("Rover".to_string()))
        .expect("unable to store dog");
}
