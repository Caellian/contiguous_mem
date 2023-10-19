#![feature(ptr_metadata)]

use contiguous_mem::{memory::DefaultMemoryManager, types::ImplDefault, *};

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
    let mut storage = ContiguousMemory::<ImplDefault>::with_capacity(4096);
    let person1 = storage.push(Person("Joe".to_string()));

    let person2: EntryRef<dyn Greetable, _> = storage.push(Person("Craig".to_string())).into_dyn();

    let dog: EntryRef<dyn Greetable, _> = storage.push(Dog("Rover".to_string())).into_dyn();

    person1.get().print_hello();
    person2.get().print_hello();
    dog.get().print_hello();
}
