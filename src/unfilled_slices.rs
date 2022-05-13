use std::alloc::{alloc, handle_alloc_error};
use std::alloc::{Layout, LayoutError};
use std::mem::MaybeUninit;
use std::ops::{Index, IndexMut, Range};
use std::ptr::NonNull;

#[cfg(has_ptr_slice_from_raw_parts)]
use core::ptr::slice_from_raw_parts_mut as slice_from_raw_parts;
#[cfg(not(has_ptr_slice_from_raw_parts))]
use core::slice::from_raw_parts_mut as slice_from_raw_parts;

#[repr(C)]
pub struct UnfilledSlice<T> {
    // with C repr we make sure this field is the first
    length: usize,
    data: [MaybeUninit<T>],
}

#[inline]
unsafe fn set_unchecked<T>(data: &mut [MaybeUninit<T>], index: usize, item: T) {
    data.get_unchecked_mut(index).write(item);
}

#[inline]
unsafe fn to_initialised_slice<T>(data: &[MaybeUninit<T>]) -> &[T] {
    &*(data as *const [MaybeUninit<T>] as *const [T])
}

#[inline]
unsafe fn to_initialised_slice_mut<T>(data: &mut [MaybeUninit<T>]) -> &mut [T] {
    &mut *(data as *mut [MaybeUninit<T>] as *mut [T])
}

impl<T> UnfilledSlice<T> {
    #[inline]
    unsafe fn get_unchecked_ref(&self, index: usize) -> &T {
        self.data.get_unchecked(index).assume_init_ref()
    }

    #[inline]
    unsafe fn get_unchecked_range_ref(&self, range: Range<usize>) -> &[T] {
        let maybe_uninit_slice = self.data.get_unchecked(range);
        to_initialised_slice(maybe_uninit_slice)
    }

    #[inline]
    unsafe fn get_unchecked_range_mut(&mut self, range: Range<usize>) -> &mut [T] {
        let maybe_uninit_slice = self.data.get_unchecked_mut(range);
        to_initialised_slice_mut(maybe_uninit_slice)
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

    #[inline]
    fn compute_layout(capacity: usize) -> Result<Layout, LayoutError> {
        let items_layout = Layout::new::<T>().repeat(capacity)?.0;
        let layout = Layout::new::<usize>()
            .extend(items_layout)?
            .0
            .pad_to_align();
        Ok(layout)
    }

    const INITIAL_LENGTH: usize = 0;

    #[inline]
    fn initialize_header(non_null_ptr: &NonNull<()>) {
        let header_ptr: *mut usize = non_null_ptr.as_ptr().cast::<usize>();
        // we initialize field length
        unsafe { std::ptr::write(header_ptr, Self::INITIAL_LENGTH) };
    }

    #[inline]
    fn to_unfilled_slice_box(non_null_ptr: &NonNull<()>, capacity: usize) -> Box<UnfilledSlice<T>> {
        let item_ptr: *mut MaybeUninit<T> = non_null_ptr.as_ptr().cast::<MaybeUninit<T>>();
        // This is where we obtain a fat reference including the capacity.
        // We do it by tricking the type system into believing we have a pointer to
        // a MaybeUninit<T> rather than to a UnfilledSlice<T> and we use it to
        // create a slice of type [MaybeUninit<T>].
        let slice_fat_ref: &mut [MaybeUninit<T>] =
            unsafe { slice_from_raw_parts(item_ptr, capacity) };
        // Then we retype the result into the correct type while preserving the fat
        // pointer.
        let uslice_fat_ptr: *mut UnfilledSlice<T> =
            slice_fat_ref as *mut [MaybeUninit<T>] as *mut UnfilledSlice<T>;

        unsafe { Box::from_raw(uslice_fat_ptr) }
    }

    pub fn new(capacity: usize) -> Box<UnfilledSlice<T>> {
        let layout = Self::compute_layout(capacity).expect("Cannot allocate that many items");

        let non_null_ptr: NonNull<()> = NonNull::new(unsafe { alloc(layout) } as *mut ())
            .unwrap_or_else(|| handle_alloc_error(layout));
        Self::initialize_header(&non_null_ptr);
        Self::to_unfilled_slice_box(&non_null_ptr, capacity)
    }

    pub const fn capacity(&self) -> usize {
        self.data.len()
    }

    pub const fn len(&self) -> usize {
        self.length
    }

    pub const fn is_empty(&self) -> bool {
        self.length == 0
    }

    pub const fn is_full(&self) -> bool {
        self.length == self.data.len()
    }

    pub fn try_add(&mut self, item: T) -> Result<(), T> {
        if self.length == self.data.len() {
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
            unsafe { self.drop_unchecked(i) }
        }
    }

    pub fn pour_end<U>(
        &mut self,
        _destination: &mut UnfilledSlice<U>,
        _f: impl FnMut(T) -> U,
    ) -> usize {
        unimplemented!()
    }

    pub fn drain_from(&mut self, _index: usize) -> std::vec::Drain<'_, T> {
        unimplemented!()
    }
}

impl<T> Index<usize> for UnfilledSlice<T> {
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

impl<T> Index<Range<usize>> for UnfilledSlice<T> {
    type Output = [T];
    fn index(&self, range: Range<usize>) -> &Self::Output {
        if self.length <= range.end {
            panic!(
                "index out of bounds: the len is {} but the range is {}..{}",
                self.length, range.start, range.end
            )
        }
        let range = range.start.min(range.end)..range.end;
        unsafe { self.get_unchecked_range_ref(range) }
    }
}

impl<T> IndexMut<usize> for UnfilledSlice<T> {
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

impl<T> IndexMut<Range<usize>> for UnfilledSlice<T> {
    fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
        if self.length <= range.end {
            panic!(
                "index out of bounds: the len is {} but the range is {}..{}",
                self.length, range.start, range.end
            )
        }
        let range = range.start.min(range.end)..range.end;
        unsafe { self.get_unchecked_range_mut(range) }
    }
}

impl<T> Drop for UnfilledSlice<T> {
    fn drop(&mut self) {
        self.clear()
    }
}
