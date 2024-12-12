use {
    crate::geometric::*,
    std::ops::{Index, IndexMut},
};

/// A struct representing a rectangle with elements of type `T`.
///
/// # Examples
///
/// ```
/// use adventofcode::{geometric::Vec2, rect::Rect};
///
/// let rect1 = Rect::new((3, 4), "Hello");
/// assert_eq!(rect1.get(&(1, 2)), Some(&"Hello"));
/// assert_eq!(rect1.get(&(8, -2)), None);
/// let mut rect2: Rect<Option<bool>> = Rect::new((3, 4), None);
/// rect2.set(&(0, 0), Some(true));
/// assert_eq!(rect2.get(&(0, 0)), Some(&Some(true)));
/// if let Some(p) = rect2.get_mut(&(1, 1)) {
///      *p = Some(false);
/// }
/// assert_eq!(rect2.get(&(1, 1)), Some(&Some(false)));
/// ```
pub struct Rect<T: Clone + Sized> {
    size: Vec2,
    vec: Vec<T>,
}

impl<T: Clone + Sized> Rect<T> {
    pub fn new(size: Vec2, default: T) -> Rect<T> {
        Rect {
            size,
            vec: vec![default; (size.0.max(0) * size.1.max(0)) as usize],
        }
    }
    #[inline]
    pub fn get(&self, index: &Vec2) -> Option<&T> {
        self.to_index(index).and_then(|i| self.vec.get(i))
    }
    #[inline]
    pub fn get_mut(&mut self, index: &Vec2) -> Option<&mut T> {
        self.to_index(index).and_then(|i| self.vec.get_mut(i))
    }
    #[inline]
    pub fn set(&mut self, index: &Vec2, val: T) {
        if let Some(i) = self.to_index(index) {
            self.vec[i] = val;
        }
    }
    #[inline]
    pub fn to_index(&self, index: &Vec2) -> Option<usize> {
        if (0..self.size.0).contains(&index.0) && (0..self.size.1).contains(&index.1) {
            Some((index.0 * self.size.1 + index.1) as usize)
        } else {
            None
        }
    }
}

impl<T: Clone + Sized> Index<&Vec2> for Rect<T> {
    type Output = T;
    #[inline]
    fn index(&self, i: &Vec2) -> &Self::Output {
        self.get(i).unwrap()
    }
}

impl<T: Clone + Sized> IndexMut<&Vec2> for Rect<T> {
    #[inline]
    fn index_mut(&mut self, i: &Vec2) -> &mut Self::Output {
        self.get_mut(i).unwrap()
    }
}

#[cfg(test)]
mod test {
    use crate::rect::Rect;

    #[test]
    fn test_index() {
        let r: Rect<bool> = Rect::new((10, 10), false);
        assert_eq!(r[&(0, 1)], false);
    }

    #[test]
    fn test_index_mut() {
        let mut r: Rect<bool> = Rect::new((10, 10), false);
        r[&(1, 1)] = true;
        assert_eq!(r[&(1, 1)], true);
    }
    #[test]
    fn test_sum() {
        let mut r: Rect<usize> = Rect::new((10, 10), 0);
        for i in 0..10 {
            for j in 0..10 {
                r[&(i, j)] = i as usize;
            }
        }
        let mut count = 0;
        for i in 0..10 {
            for j in 0..10 {
                count += r[&(i, j)];
            }
        }
        assert_eq!(count, 450);
    }
}
