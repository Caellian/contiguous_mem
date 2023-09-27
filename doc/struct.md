
 A contiguous growable array type, written as `Vec<T>`, short for 'vector'.

 # Examples

 ```
 let mut vec = Vec::new();
 vec.push(1);
 vec.push(2);

 assert_eq!(vec.len(), 2);
 assert_eq!(vec[0], 1);

 assert_eq!(vec.pop(), Some(2));
 assert_eq!(vec.len(), 1);

 vec[0] = 7;
 assert_eq!(vec[0], 7);

 vec.extend([1, 2, 3]);

 for x in &vec {
     println!("{x}");
 }
 assert_eq!(vec, [7, 1, 2, 3]);
 ```

 The [`vec!`] macro is provided for convenient initialization:

 ```
 let mut vec1 = vec![1, 2, 3];
 vec1.push(4);
 let vec2 = Vec::from([1, 2, 3, 4]);
 assert_eq!(vec1, vec2);
 ```

 It can also initialize each element of a `Vec<T>` with a given value.
 This may be more efficient than performing allocation and initialization
 in separate steps, especially when initializing a vector of zeros:

 ```
 let vec = vec![0; 5];
 assert_eq!(vec, [0, 0, 0, 0, 0]);

 // The following is equivalent, but potentially slower:
 let mut vec = Vec::with_capacity(5);
 vec.resize(5, 0);
 assert_eq!(vec, [0, 0, 0, 0, 0]);
 ```

 For more information, see
 [Capacity and Reallocation](#capacity-and-reallocation).

 Use a `Vec<T>` as an efficient stack:

 ```
 let mut stack = Vec::new();

 stack.push(1);
 stack.push(2);
 stack.push(3);

 while let Some(top) = stack.pop() {
     // Prints 3, 2, 1
     println!("{top}");
 }
 ```

 # Indexing

 The `Vec` type allows access to values by index, because it implements the
 [`Index`] trait. An example will be more explicit:

 ```
 let v = vec![0, 2, 4, 6];
 println!("{}", v[1]); // it will display '2'
 ```

 However be careful: if you try to access an index which isn't in the `Vec`,
 your software will panic! You cannot do this:

 ```should_panic
 let v = vec![0, 2, 4, 6];
 println!("{}", v[6]); // it will panic!
 ```

 Use [`get`] and [`get_mut`] if you want to check whether the index is in
 the `Vec`.

 # Slicing

 A `Vec` can be mutable. On the other hand, slices are read-only objects.
 To get a [slice][prim@slice], use [`&`]. Example:

 ```
 fn read_slice(slice: &[usize]) {
     // ...
 }

 let v = vec![0, 1];
 read_slice(&v);

 // ... and that's all!
 // you can also do it like this:
 let u: &[usize] = &v;
 // or like this:
 let u: &[_] = &v;
 ```

 In Rust, it's more common to pass slices as arguments rather than vectors
 when you just want to provide read access. The same goes for [`String`] and
 [`&str`].

 # Capacity and reallocation

 The capacity of a vector is the amount of space allocated for any future
 elements that will be added onto the vector. This is not to be confused with
 the *length* of a vector, which specifies the number of actual elements
 within the vector. If a vector's length exceeds its capacity, its capacity
 will automatically be increased, but its elements will have to be
 reallocated.

 For example, a vector with capacity 10 and length 0 would be an empty vector
 with space for 10 more elements. Pushing 10 or fewer elements onto the
 vector will not change its capacity or cause reallocation to occur. However,
 if the vector's length is increased to 11, it will have to reallocate, which
 can be slow. For this reason, it is recommended to use [`Vec::with_capacity`]
 whenever possible to specify how big the vector is expected to get.

 # Guarantees

 Due to its incredibly fundamental nature, `Vec` makes a lot of guarantees
 about its design. This ensures that it's as low-overhead as possible in
 the general case, and can be correctly manipulated in primitive ways
 by unsafe code. Note that these guarantees refer to an unqualified `Vec<T>`.
 If additional type parameters are added (e.g., to support custom allocators),
 overriding their defaults may change the behavior.

 Most fundamentally, `Vec` is and always will be a (pointer, capacity, length)
 triplet. No more, no less. The order of these fields is completely
 unspecified, and you should use the appropriate methods to modify these.
 The pointer will never be null, so this type is null-pointer-optimized.

 However, the pointer might not actually point to allocated memory. In particular,
 if you construct a `Vec` with capacity 0 via [`Vec::new`], [`vec![]`][`vec!`],
 [`Vec::with_capacity(0)`][`Vec::with_capacity`], or by calling [`shrink_to_fit`]
 on an empty Vec, it will not allocate memory. Similarly, if you store zero-sized
 types inside a `Vec`, it will not allocate space for them. *Note that in this case
 the `Vec` might not report a [`capacity`] of 0*. `Vec` will allocate if and only
 if <code>[mem::size_of::\<T>]\() * [capacity]\() > 0</code>. In general, `Vec`'s allocation
 details are very subtle --- if you intend to allocate memory using a `Vec`
 and use it for something else (either to pass to unsafe code, or to build your
 own memory-backed collection), be sure to deallocate this memory by using
 `from_raw_parts` to recover the `Vec` and then dropping it.

 If a `Vec` *has* allocated memory, then the memory it points to is on the heap
 (as defined by the allocator Rust is configured to use by default), and its
 pointer points to [`len`] initialized, contiguous elements in order (what
 you would see if you coerced it to a slice), followed by <code>[capacity] - [len]</code>
 logically uninitialized, contiguous elements.

 A vector containing the elements `'a'` and `'b'` with capacity 4 can be
 visualized as below. The top part is the `Vec` struct, it contains a
 pointer to the head of the allocation in the heap, length and capacity.
 The bottom part is the allocation on the heap, a contiguous memory block.

 ```text
             ptr      len  capacity
        +--------+--------+--------+
        | 0x0123 |      2 |      4 |
        +--------+--------+--------+
             |
             v
 Heap   +--------+--------+--------+--------+
        |    'a' |    'b' | uninit | uninit |
        +--------+--------+--------+--------+
 ```

 - **uninit** represents memory that is not initialized, see [`MaybeUninit`].
 - Note: the ABI is not stable and `Vec` makes no guarantees about its memory
   layout (including the order of fields).

 `Vec` will never perform a "small optimization" where elements are actually
 stored on the stack for two reasons:

 * It would make it more difficult for unsafe code to correctly manipulate
   a `Vec`. The contents of a `Vec` wouldn't have a stable address if it were
   only moved, and it would be more difficult to determine if a `Vec` had
   actually allocated memory.

 * It would penalize the general case, incurring an additional branch
   on every access.

 `Vec` will never automatically shrink itself, even if completely empty. This
 ensures no unnecessary allocations or deallocations occur. Emptying a `Vec`
 and then filling it back up to the same [`len`] should incur no calls to
 the allocator. If you wish to free up unused memory, use
 [`shrink_to_fit`] or [`shrink_to`].

 [`push`] and [`insert`] will never (re)allocate if the reported capacity is
 sufficient. [`push`] and [`insert`] *will* (re)allocate if
 <code>[len] == [capacity]</code>. That is, the reported capacity is completely
 accurate, and can be relied on. It can even be used to manually free the memory
 allocated by a `Vec` if desired. Bulk insertion methods *may* reallocate, even
 when not necessary.

 `Vec` does not guarantee any particular growth strategy when reallocating
 when full, nor when [`reserve`] is called. The current strategy is basic
 and it may prove desirable to use a non-constant growth factor. Whatever
 strategy is used will of course guarantee *O*(1) amortized [`push`].

 `vec![x; n]`, `vec![a, b, c, d]`, and
 [`Vec::with_capacity(n)`][`Vec::with_capacity`], will all produce a `Vec`
 with exactly the requested capacity. If <code>[len] == [capacity]</code>,
 (as is the case for the [`vec!`] macro), then a `Vec<T>` can be converted to
 and from a [`Box<[T]>`][owned slice] without reallocating or moving the elements.

 `Vec` will not specifically overwrite any data that is removed from it,
 but also won't specifically preserve it. Its uninitialized memory is
 scratch space that it may use however it wants. It will generally just do
 whatever is most efficient or otherwise easy to implement. Do not rely on
 removed data to be erased for security purposes. Even if you drop a `Vec`, its
 buffer may simply be reused by another allocation. Even if you zero a `Vec`'s memory
 first, that might not actually happen because the optimizer does not consider
 this a side-effect that must be preserved. There is one case which we will
 not break, however: using `unsafe` code to write to the excess capacity,
 and then increasing the length to match, is always valid.

 Currently, `Vec` does not guarantee the order in which elements are dropped.
 The order has changed in the past and may change again.

 [`get`]: slice::get
 [`get_mut`]: slice::get_mut
 [`String`]: crate::string::String
 [`&str`]: type@str
 [`shrink_to_fit`]: Vec::shrink_to_fit
 [`shrink_to`]: Vec::shrink_to
 [capacity]: Vec::capacity
 [`capacity`]: Vec::capacity
 [mem::size_of::\<T>]: core::mem::size_of
 [len]: Vec::len
 [`len`]: Vec::len
 [`push`]: Vec::push
 [`insert`]: Vec::insert
 [`reserve`]: Vec::reserve
 [`MaybeUninit`]: core::mem::MaybeUninit
 [owned slice]: Box