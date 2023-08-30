#![feature(ptr_metadata)]

use contiguous_mem::{ContiguousMemoryRef, GrowableContiguousMemory};

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
    let person1 = storage.store(Person("Joe".to_string()));

    let person2: ContiguousMemoryRef<dyn Greetable> =
        storage.store(Person("Craig".to_string())).into_dyn();

    let dog: ContiguousMemoryRef<dyn Greetable> =
        storage.store(Dog("Rover".to_string())).into_dyn();

    person1.print_hello();
    person2.print_hello();
    dog.print_hello();
}
