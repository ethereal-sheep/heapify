//! A collection of convenience functions for heapifying a slice in `rust`.
//!
//! # Quick Start
//! A simple way to use `heapify` is with a `Vec<T>`.
//! ``` rust
//! use heapify::*;
//! let mut vec = vec![5, 7, 9];
//! make_heap(&mut vec);
//!
//! pop_heap(&mut vec);
//! assert_eq!(vec.pop(), Some(9));
//!
//! pop_heap(&mut vec);
//! assert_eq!(vec.pop(), Some(7));
//!
//! assert_eq!(peek_heap(&mut vec), Some(&5));
//! ```

#![warn(rust_2018_idioms)]

/// Transforms the given slice into a maximal heap.
///
/// After `make_heap` is called the maximal element of the slice is located
/// at `slice[0]`.
///
/// # Examples
///
/// ```
/// use heapify::*;
/// let mut arr = [5, 7, 9];
/// make_heap(&mut arr);
/// assert_eq!(arr[0], 9);
/// assert_eq!(peek_heap(&mut arr), Some(&9));
/// ```
pub fn make_heap<T: PartialOrd>(slice: &mut [T]) {
    let n = slice.len();
    for i in (0..((n - 1) / 2)).rev() {
        bubble_down(slice, i);
    }
}

/// Pushes an element into a heap.
///
/// Given a slice where `slice[0..len-1]` is a heap, then the element at
/// `slice[len-1]` is pushed into the heap by bubbling it up to its correct
/// position.
///
/// # Examples
///
/// ```
/// use heapify::*;
/// let mut vec = vec![5, 7, 9];
/// make_heap(&mut vec);
/// assert_eq!(peek_heap(&mut vec), Some(&9));
///
/// vec.push(8);
/// push_heap(&mut vec);
/// assert_eq!(peek_heap(&mut vec), Some(&9));
///
/// vec.push(10);
/// push_heap(&mut vec);
/// assert_eq!(peek_heap(&mut vec), Some(&10));
/// ```
pub fn push_heap<T: PartialOrd>(slice: &mut [T]) {
    bubble_up(slice);
}

/// Pops an element from a maximal heap.
///
/// Given a heap, the maximal element at `slice[0]` is moved to `slice[len-1]`
/// and the heap invariant is maintained for `slice[0..len-1]`.
///
/// # Examples
///
/// ```
/// use heapify::*;
/// let mut vec = vec![5, 7, 9];
/// make_heap(&mut vec);
/// assert_eq!(peek_heap(&mut vec), Some(&9));
///
/// pop_heap(&mut vec);
/// assert_eq!(vec.pop(), Some(9));
///
/// pop_heap(&mut vec);
/// assert_eq!(vec.pop(), Some(7));
///
/// pop_heap(&mut vec);
/// assert_eq!(vec.pop(), Some(5));
/// ```
pub fn pop_heap<T: PartialOrd>(slice: &mut [T]) {
    let n = slice.len();
    if n > 1 {
        slice.swap(0, n - 1);
        bubble_down(&mut slice[0..n - 1], 0);
    }
}

/// Safely peeks at the top element of the heap. Returns `None` if heap is
/// empty.
///
/// # Examples
///
/// ```
/// use heapify::peek_heap;
/// let mut arr = [2];
/// assert_eq!(peek_heap(&mut arr), Some(&2));
/// let mut empty = [0; 0];
/// assert_eq!(peek_heap(&mut empty), None);
/// ```
pub fn peek_heap<T: PartialOrd>(slice: &mut [T]) -> Option<&T> {
    let n = slice.len();
    if n > 0 {
        Some(&slice[0])
    } else {
        None
    }
}

fn bubble_up<T: PartialOrd>(slice: &mut [T]) {
    let n = slice.len();
    let mut i = n;
    let mut p = i / 2;
    while p > 0 && (slice[p - 1] < slice[i - 1]) {
        slice.swap(p - 1, i - 1);
        i = p;
        p = i / 2;
    }
}

fn bubble_down<T: PartialOrd>(slice: &mut [T], index: usize) {
    let n = slice.len();
    let mut i = index;
    let mut l = i * 2 + 1;
    let mut r = i * 2 + 2;

    if r < n && slice[r] > slice[l] {
        l = r;
    }
    // invariant: slice[l] >= slice[r]
    // if slice[l] > slice[i], do push
    while l < n && slice[l] > slice[i] {
        slice.swap(i, l);
        i = l;
        l = i * 2 + 1;
        r = i * 2 + 2;
        if r < n && slice[r] > slice[l] {
            l = r;
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_peek_heap() {
        let mut arr = [2];
        assert_eq!(peek_heap(&mut arr), Some(&2));
        let mut empty = [0; 0];
        assert_eq!(peek_heap(&mut empty), None);
    }

    #[test]
    fn test_make_heap() {
        let mut arr = [5, 7, 9];
        make_heap(&mut arr);
        assert_eq!(arr[0], 9);
        assert_eq!(peek_heap(&mut arr), Some(&9));
    }

    #[test]
    fn test_push_heap() {
        let mut vec = vec![5, 7, 9];
        make_heap(&mut vec);
        assert_eq!(peek_heap(&mut vec), Some(&9));

        vec.push(8);
        push_heap(&mut vec);
        assert_eq!(peek_heap(&mut vec), Some(&9));

        vec.push(10);
        push_heap(&mut vec);
        assert_eq!(peek_heap(&mut vec), Some(&10));
    }

    #[test]
    fn test_pop_heap() {
        let mut vec = vec![5, 7, 9];
        make_heap(&mut vec);
        assert_eq!(peek_heap(&mut vec), Some(&9));

        pop_heap(&mut vec);
        assert_eq!(vec.pop(), Some(9));

        pop_heap(&mut vec);
        assert_eq!(vec.pop(), Some(7));

        pop_heap(&mut vec);
        assert_eq!(vec.pop(), Some(5));
    }
}
