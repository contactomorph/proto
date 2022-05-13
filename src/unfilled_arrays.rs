use std::mem::MaybeUninit;
use std::ops::{Index, IndexMut};

pub struct UnfilledArray<T, const C: usize> {
    length: usize,
    data: [MaybeUninit<T>; C],
}

#[inline]
fn new_uninit_array<T, const C: usize>() -> [MaybeUninit<T>; C] {
    unsafe { MaybeUninit::<[MaybeUninit<T>; C]>::uninit().assume_init() }
}

#[inline]
unsafe fn set_unchecked<T, const C: usize>(data: &mut [MaybeUninit<T>; C], index: usize, item: T) {
    data.get_unchecked_mut(index).write(item);
}

impl<T, const C: usize> UnfilledArray<T, C> {
    #[inline]
    unsafe fn get_unchecked_ref(&self, index: usize) -> &T {
        self.data.get_unchecked(index).assume_init_ref()
    }

    #[inline]
    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        self.data.get_unchecked_mut(index).assume_init_mut()
    }

    #[inline]
    unsafe fn move_unchecked(&mut self, index: usize) -> T {
        self.data.get_unchecked(index).assume_init_read()
    }

    #[inline]
    unsafe fn drop_unchecked(&mut self, index: usize) {
        self.data.get_unchecked_mut(index).assume_init_drop()
    }

    pub fn new() -> UnfilledArray<T, C> {
        let data = new_uninit_array();
        UnfilledArray { length: 0, data }
    }

    pub fn from_initializer(length: usize, mut f: impl FnMut() -> T) -> UnfilledArray<T, C> {
        if C < length {
            panic!(
                "length out of bounds: the capacity is {} but the length is {}",
                C, length,
            )
        }
        let mut data = new_uninit_array();
        for i in 0..length {
            unsafe {
                set_unchecked(&mut data, i, f());
            }
        }
        UnfilledArray { length, data }
    }

    pub const fn len(&self) -> usize {
        self.length
    }

    pub const fn is_empty(&self) -> bool {
        self.length == 0
    }

    pub const fn is_full(&self) -> bool {
        self.length == C
    }

    pub fn extract<U>(&mut self, mut f: impl FnMut(T) -> U) -> UnfilledArray<U, C> {
        let mut data = new_uninit_array();
        let length = self.length;
        self.length = 0;
        for i in 0..length {
            unsafe {
                let item: T = self.move_unchecked(i);
                set_unchecked(&mut data, i, f(item));
            }
        }
        UnfilledArray { length, data }
    }

    pub fn project<U, const K: usize>(&mut self, mut f: impl FnMut(T) -> U) -> UnfilledArray<U, K> {
        let mut data = new_uninit_array::<U, K>();
        let previous_length = self.length;
        let new_length = previous_length.min(K);
        self.length = 0;
        for i in 0..new_length {
            unsafe {
                let item: T = self.move_unchecked(i);
                set_unchecked(&mut data, i, f(item));
            }
        }
        for i in new_length..previous_length {
            unsafe {
                self.drop_unchecked(i);
            }
        }
        UnfilledArray {
            length: new_length,
            data,
        }
    }

    pub fn try_add(&mut self, item: T) -> Result<(), T> {
        if self.length == C {
            Err(item)
        } else {
            unsafe { set_unchecked(&mut self.data, self.length, item) };
            self.length += 1;
            Ok(())
        }
    }

    pub fn back(&self) -> Option<&T> {
        if self.length == 0 {
            return None;
        }
        Some(unsafe { self.get_unchecked_ref(self.length - 1) })
    }

    pub fn back_mut(&mut self) -> Option<&mut T> {
        if self.length == 0 {
            return None;
        }
        Some(unsafe { self.get_unchecked_mut(self.length - 1) })
    }

    pub fn pop_back(&mut self) -> Option<T> {
        if self.length == 0 {
            return None;
        }
        self.length -= 1;
        Some(unsafe { self.move_unchecked(self.length) })
    }

    pub fn truncate_from(&mut self, index: usize) -> usize {
        if self.length <= index {
            return 0;
        }
        let length = self.length;
        self.length = index;
        for i in index..length {
            unsafe { self.drop_unchecked(i) };
        }
        length - index
    }

    pub fn clear(&mut self) {
        let length = self.length;
        self.length = 0;
        for i in 0..length {
            unsafe { self.drop_unchecked(i) };
        }
    }
}

impl<T, const C: usize> std::convert::AsMut<[T]> for UnfilledArray<T, C> {
    fn as_mut(&mut self) -> &mut [T] {
        let ptr = &mut self.data as *mut MaybeUninit<T>;
        unsafe { std::slice::from_raw_parts_mut(ptr as *mut T, self.length) }
    }
}

impl<T, const C: usize> std::convert::AsRef<[T]> for UnfilledArray<T, C> {
    fn as_ref(&self) -> &[T] {
        let ptr = &self.data as *const MaybeUninit<T>;
        unsafe { std::slice::from_raw_parts(ptr as *const T, self.length) }
    }
}

impl<T, const C: usize> std::borrow::Borrow<[T]> for UnfilledArray<T, C> {
    fn borrow(&self) -> &[T] {
        self.as_ref()
    }
}

impl<T, const C: usize> std::borrow::BorrowMut<[T]> for UnfilledArray<T, C> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_mut()
    }
}

impl<T, const C: usize> PartialEq for UnfilledArray<T, C>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.length != other.length {
            return false;
        }
        for i in 0..self.length {
            let item1 = unsafe { self.get_unchecked_ref(i) };
            let item2 = unsafe { other.get_unchecked_ref(i) };
            if item1.eq(item2) {
                return false;
            }
        }
        true
    }
}

impl<T, const C: usize> Eq for UnfilledArray<T, C> where T: Eq {}

impl<T, const C: usize> Clone for UnfilledArray<T, C>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let mut data = new_uninit_array();
        for i in 0..self.length {
            unsafe {
                let item = self.get_unchecked_ref(i);
                set_unchecked(&mut data, i, item.clone());
            }
        }
        UnfilledArray {
            length: self.length,
            data,
        }
    }
}

impl<T, const C: usize> Index<usize> for UnfilledArray<T, C> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        if self.length <= index {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.length, index,
            )
        }
        unsafe { self.get_unchecked_ref(index) }
    }
}

impl<T, const C: usize> IndexMut<usize> for UnfilledArray<T, C> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if self.length <= index {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.length, index,
            )
        }
        unsafe { self.get_unchecked_mut(index) }
    }
}

impl<T, const C: usize> Drop for UnfilledArray<T, C> {
    fn drop(&mut self) {
        self.clear()
    }
}

impl<T, const C: usize> Default for UnfilledArray<T, C> {
    fn default() -> Self {
        let data = new_uninit_array();
        UnfilledArray { length: 0, data }
    }
}
