#![feature(maybe_uninit_extra)]
#![feature(allocator_api)]
#![feature(slice_ptr_get)]
#![feature(alloc_layout_extra)]
extern crate alloc;

pub mod unfilled_arrays;
pub mod unfilled_slices;

#[cfg(test)]
mod tests {
    use super::unfilled_arrays::UnfilledArray;
    use super::unfilled_slices::UnfilledSlice;
    use std::rc::Rc;

    #[test]
    fn alignment_test() {
        assert_eq!(0, std::mem::size_of::<()>());
        assert_eq!(1, std::mem::align_of::<()>());

        assert_eq!(1, std::mem::size_of::<u8>());
        assert_eq!(1, std::mem::align_of::<u8>());

        assert_eq!(4, std::mem::size_of::<(u16, u8)>());
        assert_eq!(2, std::mem::align_of::<(u16, u8)>());

        let usize_size = std::mem::size_of::<usize>();
        assert_eq!(2 * usize_size, std::mem::size_of::<(usize, u8)>());
        assert_eq!(usize_size, std::mem::align_of::<(usize, u8)>());
        assert_eq!(usize_size, std::mem::size_of::<(usize, ())>());
        assert_eq!(usize_size, std::mem::align_of::<(usize, ())>());

        let fpointer_size = usize_size + std::mem::size_of::<*const usize>();
        assert_eq!(
            fpointer_size,
            std::mem::size_of::<*mut UnfilledSlice<usize>>()
        );
        assert_eq!(fpointer_size, std::mem::size_of::<&UnfilledSlice<usize>>());
        assert_eq!(
            fpointer_size,
            std::mem::size_of::<Box<UnfilledSlice<usize>>>()
        );
    }

    #[test]
    #[should_panic]
    fn array_is_out_of_bound() {
        let x = UnfilledArray::<char, 22>::new();
        x[1];
    }

    #[test]
    fn add_to_array() {
        let mut x = UnfilledArray::<char, 2>::new();

        assert_eq!(0, x.len());

        assert!(x.try_add('x').is_ok());
        assert_eq!('x', x[0]);
        assert_eq!(1, x.len());

        assert!(x.try_add('p').is_ok());
        assert_eq!('x', x[0]);
        assert_eq!('p', x[1]);
        assert_eq!(2, x.len());
    }

    #[test]
    fn add_to_slice() {
        let mut x = UnfilledSlice::<char>::new(2);

        assert_eq!(0, x.len());

        assert!(x.try_add('x').is_ok());
        assert_eq!('x', x[0]);
        assert_eq!(1, x.len());

        assert!(x.try_add('p').is_ok());
        assert_eq!('x', x[0]);
        assert_eq!('p', x[1]);
        assert_eq!(2, x.len());
    }

    #[test]
    fn clear_array() {
        let counter = Rc::<()>::new(());

        let mut x = UnfilledArray::<Rc<()>, 5>::new();
        assert!(x.try_add(counter.clone()).is_ok());
        assert!(x.try_add(counter.clone()).is_ok());
        assert_eq!(3usize, Rc::strong_count(&counter));
        x.clear();
        assert_eq!(1usize, Rc::strong_count(&counter));
    }

    #[test]
    fn swap_array_item() {
        let text = String::from("Hello");
        let mut other = String::from("world");

        let mut x = UnfilledArray::<String, 6>::new();
        assert!(x.try_add(text).is_ok());
        assert_eq!("Hello", &x[0]);
        std::mem::swap(&mut x[0], &mut other);
        assert_eq!("world", &x[0]);
        assert_eq!("Hello", &other);
    }

    #[test]
    fn extract_array() {
        let text = String::from("Hello");
        let other = String::from("world");

        let mut x = UnfilledArray::<String, 3>::new();
        assert!(x.try_add(text).is_ok());
        assert!(x.try_add(other).is_ok());

        let y = x.extract(|e| e.len());
        assert_eq!(5, y[0]);
        assert_eq!(5, y[1]);
        assert_eq!(2, y.len());
    }

    #[test]
    fn extract_array_no_leak() {
        let counter1 = Rc::<()>::new(());
        let counter2 = Rc::<()>::new(());

        let mut x = UnfilledArray::<Rc<()>, 5>::new();
        assert!(x.try_add(counter1.clone()).is_ok());
        assert!(x.try_add(counter1.clone()).is_ok());
        assert_eq!(3usize, Rc::strong_count(&counter1));
        assert_eq!(1usize, Rc::strong_count(&counter2));

        let y = x.extract(|_| counter2.clone());

        assert_eq!(0, x.len());
        assert_eq!(2, y.len());

        assert_eq!(1usize, Rc::strong_count(&counter1));
        assert_eq!(3usize, Rc::strong_count(&counter2));
    }

    #[test]
    fn convert_to_slice() {
        let mut x = UnfilledArray::<usize, 5>::new();
        assert!(x.try_add(3).is_ok());
        assert!(x.try_add(4).is_ok());
        assert!(x.try_add(5).is_ok());
        assert!(x.try_add(6).is_ok());

        let r = x.as_ref();

        assert_eq!(4, r.len());

        for i in 0..4 {
            assert_eq!(x[i], r[i]);
        }

        let m = x.as_mut();

        assert_eq!(4, m.len());

        m[2] = 10;

        assert_eq!(10, x[2]);
    }

    #[test]
    fn add_to_slice_and_drop() {
        let counter = Rc::<()>::new(());

        {
            let mut x = UnfilledSlice::<Rc<()>>::new(2);

            assert_eq!(0, x.len());
            assert_eq!(2, x.capacity());
            assert_eq!(1usize, Rc::strong_count(&counter));

            assert!(x.try_add(counter.clone()).is_ok());
            assert_eq!(1, x.len());
            assert_eq!(2, x.capacity());
            assert_eq!(2usize, Rc::strong_count(&counter));

            assert!(x.try_add(counter.clone()).is_ok());
            assert_eq!(2, x.len());
            assert_eq!(2, x.capacity());
            assert_eq!(3usize, Rc::strong_count(&counter));

            assert!(x.try_add(counter.clone()).is_err());
            assert_eq!(2, x.len());
            assert_eq!(2, x.capacity());
            assert_eq!(3usize, Rc::strong_count(&counter));
        }

        assert_eq!(1usize, Rc::strong_count(&counter));
    }

    #[test]
    fn get_subslice() {
        let mut x = UnfilledSlice::<usize>::new(5);
        assert!(x.try_add(3).is_ok());
        assert!(x.try_add(4).is_ok());
        assert!(x.try_add(5).is_ok());
        assert!(x.try_add(6).is_ok());

        let r = &x[1..3];

        assert_eq!(2, r.len());

        for i in 0..2 {
            assert_eq!(x[i + 1], r[i]);
        }
    }
}
