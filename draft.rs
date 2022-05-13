use core::{
    alloc::{Layout, LayoutErr},
    cmp,
};

#[inline]
pub(crate) fn extend_layout(this: &Layout, next: Layout) -> Result<(Layout, usize), LayoutErr> {
    let new_align = cmp::max(this.align(), next.align());
    let pad = layout_padding_needed_for(&this, next.align());
    let offset = this.size().checked_add(pad).ok_or_else(layout_err)?;
    let new_size = offset.checked_add(next.size()).ok_or_else(layout_err)?;
    let layout = Layout::from_size_align(new_size, new_align)?;
    Ok((layout, offset))
}

#[inline]
pub(crate) fn pad_layout_to_align(this: &Layout) -> Layout {
    let pad = layout_padding_needed_for(this, this.align());
    let new_size = this.size() + pad;
    unsafe { Layout::from_size_align_unchecked(new_size, this.align()) }
}

#[inline]
pub(crate) fn layout_array<T>(n: usize) -> Result<Layout, LayoutErr> {
    repeat_layout(&Layout::new::<T>(), n).map(|(k, _)| k)
}

#[inline]
pub(crate) fn repr_c_3(fields: [Layout; 3]) -> Result<(Layout, [usize; 3]), LayoutErr> {
    let mut offsets: [usize; 3] = [0; 3];
    let mut layout = fields[0];
    for i in 1..3 {
        let (new_layout, this_offset) = extend_layout(&layout, fields[i])?;
        layout = new_layout;
        offsets[i] = this_offset;
    }
    Ok((pad_layout_to_align(&layout), offsets))
}

#[inline]
fn layout_padding_needed_for(this: &Layout, align: usize) -> usize {
    let len = this.size();
    let len_rounded_up = len.wrapping_add(align).wrapping_sub(1) & !align.wrapping_sub(1);
    len_rounded_up.wrapping_sub(len)
}

#[inline]
fn repeat_layout(this: &Layout, n: usize) -> Result<(Layout, usize), LayoutErr> {
    let padded_size = pad_layout_to_align(this).size();
    let alloc_size = padded_size.checked_mul(n).ok_or_else(layout_err)?;
    unsafe {
        Ok((
            Layout::from_size_align_unchecked(alloc_size, this.align()),
            padded_size,
        ))
    }
}

#[inline]
fn layout_err() -> LayoutErr {
    Layout::from_size_align(0, 0).unwrap_err()
}


#![warn(missing_docs, missing_debug_implementations)]
#![no_std]

//! Support for custom slice-based DSTs.
//!
//! By handling allocation manually, we can manually allocate the `Box` for a custom DST.
//! So long as the size lines up with what it should be, once the metadata is created,
//! Rust actually already handles the DSTs it already supports perfectly well, safely!
//! Setting them up is the hard part, which this crate handles for you.
//!
//! # Examples
//!
//! We have a tree structure! Each node holds some data and its children array.
//! In normal Rust, you would probably typically implement it something like this:
//!
//! ```rust
//! # use std::sync::Arc;
//! struct Node {
//!     data: &'static str,
//!     children: Vec<Arc<Node>>,
//! }
//!
//! let a = Node { data: "a", children: vec![] };
//! let b = Node { data: "b", children: vec![] };
//! let c = Node { data: "c", children: vec![] };
//! let abc = Node { data: "abc", children: vec![a.into(), b.into(), c.into()] };
//! ```
//!
//! With this setup, the memory layout looks vaguely like the following diagram:
//!
//! ```text
//!                                              +--------------+
//!                                              |Node          |
//!                                        +---->|data: "a"     |
//! +------------+    +---------------+    |     |children: none|
//! |Node        |    |Vec<Arc<Node>> |    |     +--------------+
//! |data: "abc" |    |[0]: +--------------+     |Node          |
//! |children: +----->|[1]: +------------------->|data: "b"     |
//! +------------+    |[2]: +--------------+     |children: none|
//!                   +---------------|    |     +--------------+
//!                                        |     |Node          |
//!                                        +---->|data: "c"     |
//!                                              |children: none|
//!                                              +--------------+
//! ```
//!
//! With this crate, however, the children array can be stored inline with the node's data:
//!
//! ```rust
//! # use std::{iter, sync::Arc}; use slice_dst::*;
//! struct Node(Arc<SliceWithHeader<&'static str, Node>>);
//!
//! let a = Node(SliceWithHeader::new("a", None));
//! let b = Node(SliceWithHeader::new("b", None));
//! let c = Node(SliceWithHeader::new("c", None));
//! // this vec is just an easy way to get an ExactSizeIterator
//! let abc = Node(SliceWithHeader::new("abc", vec![a, b, c]));
//! ```
//!
//! ```text
//!                          +-----------+
//! +-------------+          |Node       |
//! |Node         |    +---->|length: 0  |
//! |length: 3    |    |     |header: "a"|
//! |header: "abc"|    |     +-----------+
//! |slice: [0]: +-----+     |Node       |
//! |       [1]: +---------->|length: 0  |
//! |       [2]: +-----+     |header: "b"|
//! +-------------+    |     +-----------+
//!                    |     |Node       |
//!                    +---->|length: 0  |
//!                          |header: "c"|
//!                          +------------
//! ```
//!
//! The exact times you will want to use this rather than just standard types varries.
//! This is mostly useful when space optimization is very important.
//! This is still useful when using an arena: it reduces the allocations in the arena
//! in exchange for moving node payloads to the heap alongside the children array.
//!
//! # But how?
//!
//! This is possible because of the following key building blocks:
//!
//! - `Box`'s [memory layout][boxed-memory-layout] is defined and uses the
//!   [global allocator][std::alloc::Global], and is allowed to be manually allocated.
//! - [Array layout][array-layout] and [slice layout][slice-layout] are defined.
//! - [`#[repr(C)]`][repr-c-layout] allows us to make compound types with defined layout.
//! - We can turn an opaque pointer into a slice fat pointer with
//!   [`ptr::slice_from_raw_parts`][slice_from_raw_parts].
//! - We can cast a slice pointer to a pointer to our compound type
//!   in order to keep the correct fat pointer metadata.
//!
//! So with these guarantees, we can "just" manually allocate some space, initialize it
//! for some custom `repr(C)` structure, and convert it into a `Box`. From that point,
//! `Box` handles managing the memory, including deallocation or moving it into another
//! smart pointer, such as `Arc`.
//!
//!   [boxed-memory-layout]: <https://doc.rust-lang.org/stable/std/boxed/index.html#memory-layout>
//!   [array-layout]: <https://doc.rust-lang.org/stable/reference/type-layout.html#array-layout>
//!   [slice-layout]: <https://doc.rust-lang.org/stable/reference/type-layout.html#slice-layout>
//!   [repr-c-layout]: <https://doc.rust-lang.org/stable/reference/type-layout.html#reprc-structs>
//!   [std::alloc::Global]: <https://doc.rust-lang.org/stable/std/alloc/index.html#the-global_allocator-attribute>
//!
//! [`SliceDst`] defines the capabilities required of the pointee type. It must be able to
//! turn a trailing slice length into a [`Layout`] for the whole pointee, and it must provide
//! a way to turn a untyped slice pointer `*mut [()]` into a correctly typed pointer.
//!
//! The functions [`alloc_slice_dst`] and [`alloc_slice_dst_in`] provide a way
//! to allocate space for a `SliceDst` type via the global allocator.
//!
//! [`AllocSliceDst`] types are owning heap pointers that can create a new slice DST.
//! They take an initialization routine that is responsible for initializing the
//! uninitialized allocated place, and do the ceremony required to allocate the place
//! and turn it into the proper type by delgating to `SliceDst` and `alloc_slice_dst`.
//! They also handle panic/unwind safety of the initialization routine and prevent
//! leaking of the allocated place due to an initialization panic.
//!
//! [`TryAllocSliceDst`] is the potentially fallible initialization version.
//!
//! All of these pieces are the glue, but [`SliceWithHeader`] and [`StrWithHeader`]
//! put the pieces together into a safe package. They take a header and an iterator
//! (or copyable slice) and put together all of the pieces to allocate a dynamically
//! sized custom type.
//!
//! Additionaly, though not strictly required, these types store the slice length inline.
//! This gives them the ability to reconstruct pointers from fully type erased pointers
#![cfg_attr(feature = "erasable", doc = "via the [`Erasable`] trait")]
//! .

// All hail Chairity!
// The one who saves our sanity -
// blessing us with Clarity.
// Queen of popularity.
// When haboo becomes a rarity -
// we thank Yoba for Chairity.
// https://twitch.tv/thehaboo

extern crate alloc;

#[cfg(has_ptr_slice_from_raw_parts)]
use core::ptr::slice_from_raw_parts_mut as slice_from_raw_parts;
#[cfg(not(has_ptr_slice_from_raw_parts))]
use core::slice::from_raw_parts_mut as slice_from_raw_parts;
#[cfg(feature = "erasable")]
use erasable::{Erasable, ErasedPtr};
use {
    alloc::{
        alloc::{alloc, dealloc, handle_alloc_error},
        boxed::Box,
        rc::Rc,
        sync::Arc,
    },
    core::{alloc::Layout, mem::ManuallyDrop, ptr},
};

/// A custom slice-based dynamically sized type.
///
/// Unless you are making a custom slice DST that needs to pack its length extremely well,
/// then you should just use [`SliceWithHeader`] instead.
pub unsafe trait SliceDst {
    /// Get the layout of the slice-containing type with the given slice length.
    fn layout_for(len: usize) -> Layout;

    /// Add the type onto an untyped pointer.
    ///
    /// This is used to add the type on during allocation.
    /// This function is required because otherwise Rust cannot
    /// guarantee that the metadata on both sides of the cast lines up.
    ///
    /// # Safety
    ///
    /// The implementation _must not_ dereference the input pointer.
    /// This function is safe because it must work for all input pointers,
    /// without asserting the pointer's validity of any kind, express or implied,
    /// including but not limited to the validities of alignment, fitness for
    /// dereferencing and nullity.
    ///
    /// In practice, this means that the implementation should just be a pointer cast.
    fn retype(ptr: ptr::NonNull<[()]>) -> ptr::NonNull<Self>;
}

unsafe impl<T> SliceDst for [T] {
    fn layout_for(len: usize) -> Layout {
        layout_polyfill::layout_array::<T>(len).unwrap()
    }

    fn retype(ptr: ptr::NonNull<[()]>) -> ptr::NonNull<Self> {
        unsafe { ptr::NonNull::new_unchecked(ptr.as_ptr() as *mut _) }
    }
}

/// Allocate a slice-based DST with the [global allocator][`alloc()`].
///
/// The returned pointer is owned and completely uninitialized;
/// you are required to initialize it correctly.
///
/// If the type to be allocated has zero size,
/// then an arbitrary aligned dangling nonnull pointer is returned.
pub fn alloc_slice_dst<S: ?Sized + SliceDst>(len: usize) -> ptr::NonNull<S> {
    alloc_slice_dst_in(|it| it, len)
}

/// Allocate a slice-based DST with the [global allocator][`alloc()`] within some container.
///
/// The returned pointer is owned and completely uninitialized;
/// you are required to initialize it correctly.
///
/// Note that while this function returns a `ptr::NonNull<S>`,
/// the pointer is to the allocation as specified by `container(S::layout(len))`,
/// so if you want/need a pointer to `S`, you will need to offset it.
///
/// If the layout to be allocated has zero size,
/// then an arbitrary aligned dangling nonnull pointer is returned.
pub fn alloc_slice_dst_in<S: ?Sized + SliceDst, F>(container: F, len: usize) -> ptr::NonNull<S>
where
    F: FnOnce(Layout) -> Layout,
{
    let layout = container(S::layout_for(len));
    unsafe {
        let ptr = if layout.size() == 0 {
            // Do not allocate in the ZST case! CAD97/pointer-utils#23
            ptr::NonNull::new(layout.align() as *mut ())
        } else {
            ptr::NonNull::new(alloc(layout) as *mut ())
        }
        .unwrap_or_else(|| handle_alloc_error(layout));
        let ptr = ptr::NonNull::new_unchecked(slice_from_raw_parts(ptr.as_ptr(), len));
        S::retype(ptr)
    }
}

/// Types that can allocate a custom slice DST within them.
///
/// # Implementation note
///
/// For most types, [`TryAllocSliceDst`] should be the implementation primitive.
/// This trait can then be implemented in terms of `TryAllocSliceDst`:
///
/// ```rust
/// # use {slice_dst::*, std::ptr};
/// # struct Container<T: ?Sized>(Box<T>);
/// # unsafe impl<S: ?Sized + SliceDst> TryAllocSliceDst<S> for Container<S> {
/// #     unsafe fn try_new_slice_dst<I, E>(len: usize, init: I) -> Result<Self, E>
/// #     where I: FnOnce(ptr::NonNull<S>) -> Result<(), E>
/// #     { unimplemented!() }
/// # }
/// unsafe impl<S: ?Sized + SliceDst> AllocSliceDst<S> for Container<S> {
///     unsafe fn new_slice_dst<I>(len: usize, init: I) -> Self
///     where
///         I: FnOnce(ptr::NonNull<S>),
///     {
///         enum Void {} // or never (!) once it is stable
///         #[allow(clippy::unit_arg)]
///         let init = |ptr| Ok::<(), Void>(init(ptr));
///         match Self::try_new_slice_dst(len, init) {
///             Ok(a) => a,
///             Err(void) => match void {},
///         }
///     }
/// }
/// ```
///
/// This is not a blanket impl due to coherence rules; if the blanket impl were present,
/// it would be impossible to implement `AllocSliceDst` instead of `TryAllocSliceDst`.
pub unsafe trait AllocSliceDst<S: ?Sized + SliceDst> {
    /// Create a new custom slice DST.
    ///
    /// # Safety
    ///
    /// `init` must properly initialize the object behind the pointer.
    /// `init` receives a fully uninitialized pointer and must not read anything before writing.
    unsafe fn new_slice_dst<I>(len: usize, init: I) -> Self
    where
        I: FnOnce(ptr::NonNull<S>);
}

// FUTURE: export? Would need better generic support.
macro_rules! impl_alloc_by_try_alloc {
    ($T:ident) => {
        unsafe impl<S: ?Sized + SliceDst> $crate::AllocSliceDst<S> for $T<S> {
            unsafe fn new_slice_dst<I>(len: usize, init: I) -> Self
            where
                I: FnOnce(::core::ptr::NonNull<S>),
            {
                enum Void {}
                #[allow(clippy::unit_arg)]
                let init = |ptr| ::core::result::Result::<(), Void>::Ok(init(ptr));
                match <Self as $crate::TryAllocSliceDst<S>>::try_new_slice_dst(len, init) {
                    Ok(a) => a,
                    Err(void) => match void {},
                }
            }
        }
    };
}

/// Types that can allocate a custom slice DST within them,
/// given a fallible initialization function.
pub unsafe trait TryAllocSliceDst<S: ?Sized + SliceDst>: AllocSliceDst<S> + Sized {
    /// Create a new custom slice DST with a fallible initialization function.
    ///
    /// # Safety
    ///
    /// `init` must properly initialize the object behind the pointer.
    /// `init` receives a fully uninitialized pointer and must not read anything before writing.
    ///
    /// If the initialization closure panics or returns an error,
    /// the allocated place will be deallocated but not dropped.
    /// To clean up the partially initialized type, we suggest
    /// proxying creation through scope guarding types.
    unsafe fn try_new_slice_dst<I, E>(len: usize, init: I) -> Result<Self, E>
    where
        I: FnOnce(ptr::NonNull<S>) -> Result<(), E>;
}


struct RawBox<S: ?Sized + SliceDst>(ptr::NonNull<S>, Layout);

impl<S: ?Sized + SliceDst> RawBox<S> {
    unsafe fn new(len: usize) -> Self {
        let layout = S::layout_for(len);
        RawBox(alloc_slice_dst(len), layout)
    }

    unsafe fn finalize(self) -> Box<S> {
        let this = ManuallyDrop::new(self);
        Box::from_raw(this.0.as_ptr())
    }
}

impl<S: ?Sized + SliceDst> Drop for RawBox<S> {
    fn drop(&mut self) {
        unsafe {
            dealloc(self.0.as_ptr().cast(), self.1);
        }
    }
}

// SAFETY: Box is guaranteed to be allocatable by GlobalAlloc.
impl_alloc_by_try_alloc!(Box);
unsafe impl<S: ?Sized + SliceDst> TryAllocSliceDst<S> for Box<S> {
    unsafe fn try_new_slice_dst<I, E>(len: usize, init: I) -> Result<Self, E>
    where
        I: FnOnce(ptr::NonNull<S>) -> Result<(), E>,
    {
        let ptr = RawBox::new(len);
        init(ptr.0)?;
        Ok(ptr.finalize())
    }
}

// SAFETY: just delegates to `Box`'s implementation (for now?)
impl_alloc_by_try_alloc!(Rc);
unsafe impl<S: ?Sized + SliceDst> TryAllocSliceDst<S> for Rc<S> {
    unsafe fn try_new_slice_dst<I, E>(len: usize, init: I) -> Result<Self, E>
    where
        I: FnOnce(ptr::NonNull<S>) -> Result<(), E>,
    {
        Box::try_new_slice_dst(len, init).map(Into::into)
    }
}

// SAFETY: just delegates to `Box`'s implementation (for now?)
impl_alloc_by_try_alloc!(Arc);
unsafe impl<S: ?Sized + SliceDst> TryAllocSliceDst<S> for Arc<S> {
    unsafe fn try_new_slice_dst<I, E>(len: usize, init: I) -> Result<Self, E>
    where
        I: FnOnce(ptr::NonNull<S>) -> Result<(), E>,
    {
        Box::try_new_slice_dst(len, init).map(Into::into)
    }
}
use super::*;

#[repr(C)]
#[derive(Debug, Eq, PartialEq, Hash)]
/// A custom slice-based DST.
///
/// The length is stored as a `usize` at offset 0.
/// This _must_ be the length of the trailing slice of the DST.
pub struct SliceWithHeader<Header, Item> {
    /// Safety: must be at offset 0
    length: usize,
    /// The included header. Does not dictate the slice length.
    pub header: Header,
    /// The included slice.
    pub slice: [Item],
}

unsafe impl<Header, Item> SliceDst for SliceWithHeader<Header, Item> {
    fn layout_for(len: usize) -> Layout {
        Self::layout(len).0
    }

    fn retype(ptr: ptr::NonNull<[()]>) -> ptr::NonNull<Self> {
        unsafe { ptr::NonNull::new_unchecked(ptr.as_ptr() as *mut _) }
    }
}

impl<Header, Item> SliceWithHeader<Header, Item> {
    fn layout(len: usize) -> (Layout, [usize; 3]) {
        let length_layout = Layout::new::<usize>();
        let header_layout = Layout::new::<Header>();
        let slice_layout = layout_polyfill::layout_array::<Item>(len).unwrap();
        layout_polyfill::repr_c_3([length_layout, header_layout, slice_layout]).unwrap()
    }

    struct InProgress<Header, Item> {
        raw: ptr::NonNull<SliceWithHeader<Header, Item>>,
        written: usize,
        layout: Layout,
        length_offset: usize,
        header_offset: usize,
        slice_offset: usize,
    }

    impl<Header, Item> Drop for InProgress<Header, Item> {
        fn drop(&mut self) {
            unsafe {
                ptr::drop_in_place(slice_from_raw_parts(
                    self.raw().add(self.slice_offset).cast::<Item>(),
                    self.written,
                ));
            }
        }
    }

    impl<Header, Item> InProgress<Header, Item> {
        fn init(
            len: usize,
            header: Header,
            mut items: impl Iterator<Item = Item> + ExactSizeIterator,
        ) -> impl FnOnce(ptr::NonNull<SliceWithHeader<Header, Item>>) {
            move |ptr| {
                let mut this = Self::new(len, ptr);

                unsafe {
                    for _ in 0..len {
                        let item = items
                            .next()
                            .expect("ExactSizeIterator over-reported length");
                        this.push(item);
                    }

                    assert!(
                        items.next().is_none(),
                        "ExactSizeIterator under-reported length"
                    );

                    this.finish(len, header)
                }
            }
        }

        fn raw(&self) -> *mut u8 {
            self.raw.as_ptr().cast()
        }

        fn new(len: usize, raw: ptr::NonNull<SliceWithHeader<Header, Item>>) -> Self {
            let (layout, [length_offset, header_offset, slice_offset]) =
                SliceWithHeader::<Header, Item>::layout(len);
            InProgress {
                raw,
                written: 0,
                layout,
                length_offset,
                header_offset,
                slice_offset,
            }
        }

        unsafe fn push(&mut self, item: Item) {
            self.raw()
                .add(self.slice_offset)
                .cast::<Item>()
                .add(self.written)
                .write(item);
            self.written += 1;
        }

        unsafe fn finish(self, len: usize, header: Header) {
            let this = ManuallyDrop::new(self);
            ptr::write(this.raw().add(this.length_offset).cast(), len);
            ptr::write(this.raw().add(this.header_offset).cast(), header);
            debug_assert_eq!(this.layout, Layout::for_value(this.raw.as_ref()))
        }
    }


    #[allow(clippy::new_ret_no_self)]
    /// Create a new slice/header DST in a [`AllocSliceDst`] container.
    ///
    /// # Panics
    ///
    /// Panics if the items iterator incorrectly reports its length.
    pub fn new<A, I>(header: Header, items: I) -> A
    where
        A: AllocSliceDst<Self>,
        I: IntoIterator<Item = Item>,
        I::IntoIter: ExactSizeIterator,
    {
        let items = items.into_iter();
        let len = items.len();
        unsafe { A::new_slice_dst(len, InProgress::init(len, header, items)) }
    }

    #[allow(clippy::new_ret_no_self)]
    /// Create a new slice/header DST from a slice, in a [`AllocSliceDst`] container.
    pub fn from_slice<A>(header: Header, s: &[Item]) -> A
    where
        A: AllocSliceDst<Self>,
        Item: Copy,
    {
        let len = s.len();
        let (layout, [length_offset, header_offset, slice_offset]) = Self::layout(len);
        unsafe {
            A::new_slice_dst(len, |ptr| {
                let raw = ptr.as_ptr().cast::<u8>();
                ptr::write(raw.add(length_offset).cast(), len);
                ptr::write(raw.add(header_offset).cast(), header);
                ptr::copy_nonoverlapping(s.as_ptr(), raw.add(slice_offset).cast(), len);
                debug_assert_eq!(Layout::for_value(ptr.as_ref()), layout);
            })
        }
    }
}

impl<Header, Item> Clone for Box<SliceWithHeader<Header, Item>>
where
    Header: Clone,
    Item: Clone,
{
    fn clone(&self) -> Self {
        SliceWithHeader::new(self.header.clone(), self.slice.iter().cloned())
    }
}

#[cfg(feature = "erasable")]
unsafe impl<Header, Item> Erasable for SliceWithHeader<Header, Item> {
    unsafe fn unerase(this: ErasedPtr) -> ptr::NonNull<Self> {
        let len: usize = ptr::read(this.as_ptr().cast());
        let raw = ptr::NonNull::new_unchecked(slice_from_raw_parts(this.as_ptr().cast(), len));
        Self::retype(raw)
    }

    const ACK_1_1_0: bool = true;
}

#[repr(C)]
#[derive(Debug, Eq, PartialEq, Hash)]
/// A custom str-based DST.
///
/// The length is stored as a `usize` at offset 0.
/// This _must_ be the length of the trailing slice.
pub struct StrWithHeader<Header> {
    /// Safety: must be at offset 0
    length: usize,
    /// The included header. Does not dictate the slice length.
    pub header: Header,
    /// The included str.
    pub str: str,
}

unsafe impl<Header> SliceDst for StrWithHeader<Header> {
    fn layout_for(len: usize) -> Layout {
        Self::layout(len).0
    }

    fn retype(ptr: ptr::NonNull<[()]>) -> ptr::NonNull<Self> {
        unsafe { ptr::NonNull::new_unchecked(ptr.as_ptr() as *mut _) }
    }
}

impl<Header> StrWithHeader<Header> {
    fn layout(len: usize) -> (Layout, [usize; 3]) {
        let length_layout = Layout::new::<usize>();
        let header_layout = Layout::new::<Header>();
        let slice_layout = layout_polyfill::layout_array::<u8>(len).unwrap();
        layout_polyfill::repr_c_3([length_layout, header_layout, slice_layout]).unwrap()
    }

    #[allow(clippy::new_ret_no_self)]
    /// Create a new str/header DST in a [`AllocSliceDst`] container.
    pub fn new<A>(header: Header, s: &str) -> A
    where
        A: AllocSliceDst<Self>,
    {
        let len = s.len();
        let (layout, [length_offset, header_offset, str_offset]) = Self::layout(len);
        unsafe {
            A::new_slice_dst(len, |ptr| {
                let raw = ptr.as_ptr().cast::<u8>();
                ptr::write(raw.add(length_offset).cast(), len);
                ptr::write(raw.add(header_offset).cast(), header);
                ptr::copy_nonoverlapping(s.as_bytes().as_ptr(), raw.add(str_offset).cast(), len);
                debug_assert_eq!(Layout::for_value(ptr.as_ref()), layout);
            })
        }
    }
}

impl<Header> Clone for Box<StrWithHeader<Header>>
where
    Header: Clone,
{
    fn clone(&self) -> Self {
        StrWithHeader::new(self.header.clone(), &self.str)
    }
}

#[cfg(feature = "erasable")]
unsafe impl<Header> Erasable for StrWithHeader<Header> {
    unsafe fn unerase(this: ErasedPtr) -> ptr::NonNull<Self> {
        let len: usize = ptr::read(this.as_ptr().cast());
        let raw = ptr::NonNull::new_unchecked(slice_from_raw_parts(this.as_ptr().cast(), len));
        Self::retype(raw)
    }

    const ACK_1_1_0: bool = true;
}