use std::{
    alloc::Layout,
    io::{Cursor, ErrorKind, Read, Write},
    mem::align_of,
};

use byteorder::{ReadBytesExt, WriteBytesExt, LE};
use contiguous_mem::*;

pub enum IndexOrPtr<T> {
    Index(u32),
    Ptr(*const T),
}
impl<T> IndexOrPtr<T> {
    pub fn to_ref(&self, data: &[*const T]) -> IndexOrPtr<T> {
        match self {
            IndexOrPtr::Index(index) => IndexOrPtr::Ptr(data[*index as usize]),
            IndexOrPtr::Ptr(ref ptr) => IndexOrPtr::Ptr(*ptr),
        }
    }

    pub fn unwrap_ptr(&self) -> *const T {
        match self {
            IndexOrPtr::Index(_) => panic!("not a pointer"),
            IndexOrPtr::Ptr(ptr) => *ptr,
        }
    }

    pub fn unwrap_ref(&self) -> &'static mut T {
        unsafe { &mut *(self.unwrap_ptr() as *mut T) }
    }
}

pub trait Load {
    unsafe fn load<R: Read>(data: R) -> Self;
}
pub trait Save {
    fn save<W: Write>(&self, data: &mut W) -> Result<(), std::io::Error>;
}

pub struct Enemy {
    pub max_health: u32,
    pub health: u32,
    pub speed: f32,
    pub age: f32,
}
impl Enemy {
    pub fn reset(&mut self) {
        self.health = self.max_health;
        self.age = 0.0;
    }
}
impl Load for Enemy {
    unsafe fn load<R: Read>(mut data: R) -> Enemy {
        Enemy {
            max_health: data.read_u32::<LE>().unwrap_unchecked(),
            health: data.read_u32::<LE>().unwrap_unchecked(),
            speed: data.read_f32::<LE>().unwrap_unchecked(),
            age: data.read_f32::<LE>().unwrap_unchecked(),
        }
    }
}
impl Save for Enemy {
    fn save<W: Write>(&self, data: &mut W) -> Result<(), std::io::Error> {
        data.write_u32::<LE>(self.max_health)?;
        data.write_u32::<LE>(self.health)?;
        data.write_f32::<LE>(self.speed)?;
        data.write_f32::<LE>(self.age)?;
        Ok(())
    }
}

pub struct Level {
    pub enemies: Vec<IndexOrPtr<Enemy>>,
}

impl Load for Level {
    unsafe fn load<R: Read>(mut data: R) -> Level {
        let enemies_count = data.read_u32::<LE>().unwrap();
        let enemies = (0..enemies_count).map(|_| {
            let enemy_index = data.read_u32::<LE>().unwrap();
            IndexOrPtr::Index(enemy_index)
        });
        Level {
            enemies: enemies.collect(),
        }
    }
}
impl Save for Level {
    fn save<W: Write>(&self, data: &mut W) -> Result<(), std::io::Error> {
        data.write_u32::<LE>(self.enemies.len() as u32)?;
        for enemy in self.enemies.iter() {
            match enemy {
                IndexOrPtr::Index(index) => data.write_u32::<LE>(*index)?,
                IndexOrPtr::Ptr(_) => {
                    return Err(std::io::Error::new(
                        ErrorKind::InvalidData,
                        "can't save level with references",
                    ))
                }
            }
        }
        Ok(())
    }
}

// this function emulates FS access for this example, ignore it
fn load_game_file<T: Load>(file_name: &'static str) -> T {
    let mut data = Vec::with_capacity(24);
    let mut data_cursor = Cursor::new(&mut data);
    match file_name {
        "enemy1.dat" => Enemy {
            max_health: 200,
            health: 200,
            speed: 2.0,
            age: 0.0,
        }
        .save(&mut data_cursor)
        .unwrap(),
        "enemy2.dat" => Enemy {
            max_health: 200,
            health: 200,
            speed: 2.0,
            age: 0.0,
        }
        .save(&mut data_cursor)
        .unwrap(),
        "enemy3.dat" => Enemy {
            max_health: 200,
            health: 200,
            speed: 2.0,
            age: 0.0,
        }
        .save(&mut data_cursor)
        .unwrap(),
        "enemy4.dat" => Enemy {
            max_health: 200,
            health: 200,
            speed: 2.0,
            age: 0.0,
        }
        .save(&mut data_cursor)
        .unwrap(),
        "level1.dat" => Level {
            enemies: vec![
                IndexOrPtr::Index(0),
                IndexOrPtr::Index(1),
                IndexOrPtr::Index(1),
                IndexOrPtr::Index(2),
            ],
        }
        .save(&mut data_cursor)
        .unwrap(),
        "level2.dat" => Level {
            enemies: vec![
                IndexOrPtr::Index(1),
                IndexOrPtr::Index(1),
                IndexOrPtr::Index(1),
                IndexOrPtr::Index(2),
                IndexOrPtr::Index(2),
                IndexOrPtr::Index(3),
                IndexOrPtr::Index(3),
            ],
        }
        .save(&mut data_cursor)
        .unwrap(),
        _ => unreachable!(),
    };
    data_cursor.set_position(0);

    unsafe { T::load(data_cursor) }
}

fn main() {
    let mut data = UnsafeContiguousMemory::new_with_layout(
        Layout::from_size_align(112, align_of::<Level>()).unwrap(),
    );

    // Create enemy lookup list.
    let enemies: &[*const Enemy] = unsafe {
        &[
            data.push(load_game_file("enemy1.dat")).unwrap_unchecked(),
            data.push(load_game_file("enemy2.dat")).unwrap_unchecked(),
            data.push(load_game_file("enemy3.dat")).unwrap_unchecked(),
            data.push(load_game_file("enemy4.dat")).unwrap_unchecked(),
        ]
    };

    // Create level lookup list.
    let levels: &[*mut Level] = unsafe {
        &[
            data.push(load_game_file("level1.dat")).unwrap_unchecked(),
            data.push(load_game_file("level2.dat")).unwrap_unchecked(),
        ]
    };

    // data won't go out of scope while we're using it in this example, but in
    // your use case it might. This is here for completeness.
    data.forget();
    // now we can assume all created pointers are 'static

    // prepare levels for use
    levels.iter().for_each(|level| {
        let level = unsafe { &mut **level };

        level.enemies = level
            .enemies
            .iter()
            .map(|enemy| enemy.to_ref(enemies))
            .collect();
    });

    let mut time = 0.0;
    let mut current_level: usize = 0;

    // Main game loop
    while current_level < levels.len() {
        // Simulate the passage of time (you can replace this with your game logic)
        time += 1.0;

        let mut all_enemies_killed = true;
        let current_lvl = unsafe { &mut *levels[current_level] };

        for enemy in current_lvl.enemies.iter_mut() {
            let enemy_ref = enemy.unwrap_ref();

            let health_reduction = ((5.0 + time * 0.25) as u32).min(enemy_ref.health);
            enemy_ref.health -= health_reduction;
            enemy_ref.age += 1.0;

            // Check if the enemy is still alive
            if enemy_ref.health > 0 {
                all_enemies_killed = false;
            }
        }

        // If all enemies in the current level are killed, reset them and progress to the next level
        if all_enemies_killed {
            println!(
                "All enemies in level {} have been killed!",
                current_level + 1
            );
            current_level += 1;

            // Reset all enemies in the next level
            if current_level < levels.len() {
                let next_level = unsafe { &mut *levels[current_level] };
                for enemy in next_level.enemies.iter_mut() {
                    enemy.unwrap_ref().reset();
                }
            }
        }
    }

    println!(
        "Congratulations! You've completed all levels in: {:.2}",
        time
    );
}
