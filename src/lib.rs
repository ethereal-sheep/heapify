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
use core::cmp::Ordering;

/// Transforms the given slice into a maximal heap.
///
/// After `make_heap` is called, the maximal element of the slice is located
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
    make_heap_with(slice, T::partial_cmp)
}

/// Transforms the given slice into a heap with a given predicate.
///
/// After `make_heap_with` is called, the top element of the heap is located
/// at `slice[0]`.
///
/// # Examples
///
/// ```
/// use heapify::*;
/// let mut arr = [5, 7, 9];
/// make_heap_with(&mut arr, |lhs, rhs| rhs.partial_cmp(lhs));
/// assert_eq!(arr[0], 5);
/// assert_eq!(peek_heap(&mut arr), Some(&5));
/// ```
pub fn make_heap_with<T>(slice: &mut [T], pred: fn(&T, &T) -> Option<Ordering>) {
    let n = slice.len();
    for i in (0..=((n - 1) / 2)).rev() {
        bubble_down(slice, i, pred);
    }
}

/// Creates a `HeapIterator<T>` from a given slice.
///
/// # Examples
///
/// ```
/// use heapify::*;
/// let mut arr = [5, 7, 9];
/// let mut iter = make_heap_iter(&mut arr);
/// assert_eq!(iter.next().cloned(), Some(9));
/// ```
pub fn make_heap_iter<T: PartialOrd>(slice: &mut [T]) -> HeapIterator<'_, T> {
    make_heap(slice);
    HeapIterator { heap: slice }
}

/// Creates a `PredHeapIterator<T>` from a given slice and a given predicate.
///
/// # Examples
///
/// ```
/// use heapify::*;
/// let mut arr = [5, 7, 9];
/// let mut iter = make_heap_iter_with(&mut arr, |lhs, rhs| rhs.partial_cmp(lhs));
/// assert_eq!(iter.next().cloned(), Some(5));
/// ```
pub fn make_heap_iter_with<T>(
    slice: &mut [T],
    pred: fn(&T, &T) -> Option<Ordering>,
) -> PredHeapIterator<'_, T> {
    make_heap_with(slice, pred);
    PredHeapIterator { heap: slice, pred }
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
    bubble_up(slice, T::partial_cmp);
}

/// Pushes an element into a heap, with a given predicate.
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
/// make_heap_with(&mut vec, |lhs, rhs| rhs.partial_cmp(lhs));
/// assert_eq!(peek_heap(&mut vec), Some(&5));
///
/// vec.push(8);
/// push_heap_with(&mut vec, |lhs, rhs| rhs.partial_cmp(lhs));
/// assert_eq!(peek_heap(&mut vec), Some(&5));
///
/// vec.push(3);
/// push_heap_with(&mut vec, |lhs, rhs| rhs.partial_cmp(lhs));
/// assert_eq!(peek_heap(&mut vec), Some(&3));
/// ```
pub fn push_heap_with<T>(slice: &mut [T], pred: fn(&T, &T) -> Option<Ordering>) {
    bubble_up(slice, pred);
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
        bubble_down(&mut slice[0..n - 1], 0, T::partial_cmp);
    }
}
/// Pops an element from a maximal heap, with a given predicate.
///
/// Given a heap, the maximal element at `slice[0]` is moved to `slice[len-1]`
/// and the heap invariant is maintained for `slice[0..len-1]`.
///
/// # Examples
///
/// ```
/// use heapify::*;
/// let mut vec = vec![5, 7, 9];
/// make_heap_with(&mut vec, |lhs, rhs| rhs.partial_cmp(lhs));
/// assert_eq!(peek_heap(&mut vec), Some(&5));
///
/// pop_heap_with(&mut vec, |lhs, rhs| rhs.partial_cmp(lhs));
/// assert_eq!(vec.pop(), Some(5));
///
/// pop_heap_with(&mut vec, |lhs, rhs| rhs.partial_cmp(lhs));
/// assert_eq!(vec.pop(), Some(7));
///
/// pop_heap_with(&mut vec, |lhs, rhs| rhs.partial_cmp(lhs));
/// assert_eq!(vec.pop(), Some(9));
/// ```
pub fn pop_heap_with<T>(slice: &mut [T], pred: fn(&T, &T) -> Option<Ordering>) {
    let n = slice.len();
    if n > 1 {
        slice.swap(0, n - 1);
        bubble_down(&mut slice[0..n - 1], 0, pred);
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
pub fn peek_heap<T>(slice: &mut [T]) -> Option<&T> {
    let n = slice.len();
    if n > 0 {
        Some(&slice[0])
    } else {
        None
    }
}

fn pred_greater<T>(pred: fn(&T, &T) -> Option<Ordering>, lhs: &T, rhs: &T) -> bool {
    pred(lhs, rhs) == Some(Ordering::Greater)
}

fn bubble_up<T>(slice: &mut [T], pred: fn(&T, &T) -> Option<Ordering>) {
    let n = slice.len();
    let mut i = n;
    let mut p = i / 2;
    while p > 0 && (pred_greater(pred, &slice[i - 1], &slice[p - 1])) {
        slice.swap(p - 1, i - 1);
        i = p;
        p = i / 2;
    }
}

fn bubble_down<T>(slice: &mut [T], index: usize, pred: fn(&T, &T) -> Option<Ordering>) {
    let n = slice.len();
    let mut i = index;
    let mut l = i * 2 + 1;
    let mut r = i * 2 + 2;

    if r < n && pred_greater(pred, &slice[r], &slice[l]) {
        l = r;
    }
    // invariant: slice[l] >= slice[r]
    // if slice[l] > slice[i], do push
    while l < n && pred_greater(pred, &slice[l], &slice[i]) {
        slice.swap(i, l);
        i = l;
        l = i * 2 + 1;
        r = i * 2 + 2;
        if r < n && pred_greater(pred, &slice[r], &slice[l]) {
            l = r;
        }
    }
}

/// An iterator type to iterate upon a heap.
///
/// A complete iteration has the side effect of sorting the underlying
/// slice in ascending order.
///
/// # Examples
/// Basic usage:
/// ```
/// use heapify::*;
/// let mut arr = [5, 7, 9];
/// let iter = make_heap_iter(&mut arr);
/// for item in iter {
///     print!("{} ", item);
/// }
/// ```
/// This will print:
/// ``` text
/// 9 7 5
/// ```
#[derive(Debug)]
pub struct HeapIterator<'a, T: PartialOrd> {
    heap: &'a mut [T],
}

impl<'a, T: PartialOrd> core::iter::Iterator for HeapIterator<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.heap.len();
        if n > 0 {
            pop_heap(self.heap);

            unsafe {
                let old = core::ptr::read(&self.heap);
                let (left, right) = old.split_at_mut(n - 1);
                core::ptr::write(&mut self.heap, left);
                assert_eq!(right.len(), 1);

                Some(&mut right[0])
            }
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.heap.len(), Some(self.heap.len()))
    }
}

/// An iterator type to iterate upon a heap with a given predicate.
///
/// Larger than HeapIterator due to storing of the function pointer predicate.
///
/// A complete iteration has the side effect of sorting the underlying
/// slice in order provided by predicate.
///
/// # Examples
/// Basic usage:
/// ```
/// use heapify::*;
/// let mut arr = [5, 7, 9];
/// let iter = make_heap_iter_with(&mut arr, |lhs, rhs| rhs.partial_cmp(lhs));
/// for item in iter {
///     print!("{} ", item);
/// }
/// ```
/// This will print:
/// ``` text
/// 5 7 9
/// ```
pub struct PredHeapIterator<'a, T> {
    heap: &'a mut [T],
    pred: fn(&T, &T) -> Option<Ordering>,
}

impl<'a, T> core::iter::Iterator for PredHeapIterator<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.heap.len();
        if n > 0 {
            pop_heap_with(self.heap, self.pred);

            unsafe {
                let old = core::ptr::read(&self.heap);
                let (left, right) = old.split_at_mut(n - 1);
                core::ptr::write(&mut self.heap, left);
                assert_eq!(right.len(), 1);

                Some(&mut right[0])
            }
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.heap.len(), Some(self.heap.len()))
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
    fn test_make_heap_with() {
        let mut arr = [5, 7, 9];
        make_heap_with(&mut arr, |lhs, rhs| rhs.partial_cmp(lhs));
        assert_eq!(arr[0], 5);
        assert_eq!(peek_heap(&mut arr), Some(&5));
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
    fn test_push_heap_with() {
        let mut vec = vec![5, 7, 9];
        let pred: fn(&i32, &i32) -> Option<Ordering> = |lhs, rhs| rhs.partial_cmp(lhs);
        make_heap_with(&mut vec, pred);
        assert_eq!(peek_heap(&mut vec), Some(&5));

        vec.push(8);
        push_heap_with(&mut vec, pred);
        assert_eq!(peek_heap(&mut vec), Some(&5));

        vec.push(3);
        push_heap_with(&mut vec, pred);
        assert_eq!(peek_heap(&mut vec), Some(&3));
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

    #[test]
    fn test_pop_heap_with() {
        let mut vec = vec![5, 7, 9];
        let pred: fn(&i32, &i32) -> Option<Ordering> = |lhs, rhs| rhs.partial_cmp(lhs);
        make_heap_with(&mut vec, pred);
        assert_eq!(peek_heap(&mut vec), Some(&5));

        pop_heap_with(&mut vec, pred);
        assert_eq!(vec.pop(), Some(5));

        pop_heap_with(&mut vec, pred);
        assert_eq!(vec.pop(), Some(7));

        pop_heap_with(&mut vec, pred);
        assert_eq!(vec.pop(), Some(9));
    }

    #[test]
    fn test_heap_iterator_next_value() {
        let mut vec = vec![5, 7, 9];
        let mut iter = make_heap_iter(&mut vec);

        assert_eq!(iter.next().cloned(), Some(9));
        assert_eq!(iter.next().cloned(), Some(7));
        assert_eq!(iter.next().cloned(), Some(5));
    }

    #[test]
    fn test_heap_iterator_sorted() {
        let mut vec = vec![1, 9, 2, 8, 3, 7];
        let iter = make_heap_iter(&mut vec);
        for _ in iter {}
        assert_eq!(vec, vec![1, 2, 3, 7, 8, 9]);
    }

    #[test]
    fn test_heap_iterator_mut() {
        let mut vec = vec![1, 2, 3, 4, 5, 6];
        let iter = make_heap_iter(&mut vec);
        iter.for_each(|i| {
            if *i % 2 == 0 {
                *i = 0
            }
        });

        assert_eq!(vec, vec![1, 0, 3, 0, 5, 0]);
    }

    #[test]
    fn test_pred_heap_iterator_sorted() {
        let pred: fn(&i32, &i32) -> Option<Ordering> = |lhs, rhs| rhs.partial_cmp(lhs);
        let mut vec = vec![1, 9, 2, 8, 3, 7];
        let iter = make_heap_iter_with(&mut vec, pred);
        for _ in iter {}
        assert_eq!(vec, vec![9, 8, 7, 3, 2, 1]);
    }

    #[test]
    fn test_pred_heap_iterator_mut() {
        let pred: fn(&i32, &i32) -> Option<Ordering> = |lhs, rhs| rhs.partial_cmp(lhs);
        let mut vec = vec![1, 2, 3, 4, 5, 6];
        let iter = make_heap_iter_with(&mut vec, pred);
        iter.for_each(|i| {
            if *i % 2 == 1 {
                *i = 0
            }
        });

        assert_eq!(vec, vec![6, 0, 4, 0, 2, 0]);
    }
}
