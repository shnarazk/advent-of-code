use {
    crate::geometric::*,
    serde::Serialize,
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
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Rect<T: Clone + Default + Sized> {
    size: Vec2,
    vec: Vec<T>,
}

impl<T: Clone + Default + Sized> Rect<T> {
    pub fn new<V: AsReference<Vec2>>(size: V, default: T) -> Rect<T> {
        let sf = size.as_vec_ref();
        Rect {
            size: *sf,
            vec: vec![default; (sf.0.max(0) * sf.1.max(0)) as usize],
        }
    }
    pub fn from_vec(v: Vec<Vec<T>>) -> Rect<T> {
        Rect {
            size: (v.len() as isize, v[0].len() as isize),
            vec: v.into_iter().flatten().collect::<Vec<T>>(),
        }
    }
    #[inline]
    pub fn get<V: AsReference<Vec2>>(&self, index: V) -> Option<&T> {
        self.to_index(index.as_vec_ref())
            .and_then(|i| self.vec.get(i))
    }
    #[inline]
    pub fn get_unchecked<V: AsReference<Vec2>>(&self, index: V) -> &T {
        unsafe {
            self.vec
                .get_unchecked(self.to_index_unchecked(index.as_vec_ref()))
        }
    }
    #[inline]
    pub fn get_mut<V: AsReference<Vec2>>(&mut self, index: V) -> Option<&mut T> {
        self.to_index(index.as_vec_ref())
            .and_then(|i| self.vec.get_mut(i))
    }
    #[inline]
    pub fn get_mut_unchecked<V: AsReference<Vec2>>(&mut self, index: V) -> &mut T {
        let i = self.to_index_unchecked(index.as_vec_ref());
        unsafe { self.vec.get_unchecked_mut(i) }
    }
    #[inline]
    pub fn set<V: AsReference<Vec2>>(&mut self, index: V, val: T) {
        if let Some(i) = self.to_index(index.as_vec_ref()) {
            self.vec[i] = val;
        }
    }
    #[inline]
    pub fn to_index<V: AsReference<Vec2>>(&self, index: V) -> Option<usize> {
        let idx = index.as_vec_ref();
        if (0..self.size.0).contains(&idx.0) && (0..self.size.1).contains(&idx.1) {
            Some((idx.0 * self.size.1 + idx.1) as usize)
        } else {
            None
        }
    }
    #[inline]
    pub fn to_index_unchecked<V: AsReference<Vec2>>(&self, index: V) -> usize {
        let idx = index.as_vec_ref();
        (idx.0 * self.size.1 + idx.1) as usize
    }
    pub fn size(&self) -> &Vec2 {
        &self.size
    }
    pub fn iter(&self) -> Vec2Iter<T> {
        Vec2Iter {
            vec: &self.vec,
            max_j: self.size.1,
            i: 0,
            j: 0,
            index: 0,
            len: self.vec.len(),
        }
    }
    pub fn map<U: Clone + Default + Sized>(&self, f: impl Fn(&T) -> U) -> Rect<U> {
        Rect {
            size: self.size,
            vec: self.vec.iter().map(f).collect::<Vec<U>>(),
        }
    }
}

pub struct Vec2Iter<'a, T> {
    vec: &'a Vec<T>,
    max_j: isize,
    i: isize,
    j: isize,
    index: usize,
    len: usize,
}

impl<'a, T> Iterator for Vec2Iter<'a, T> {
    type Item = (Vec2, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.len {
            let ret = ((self.i, self.j), &self.vec[self.index]);
            self.j += 1;
            if self.j == self.max_j {
                self.i += 1;
                self.j = 0;
            }
            self.index += 1;
            Some(ret)
        } else {
            None
        }
    }
}

impl<V: AsReference<Vec2>, T: Clone + Default + Sized> Index<V> for Rect<T> {
    type Output = T;
    #[inline]
    fn index(&self, i: V) -> &Self::Output {
        self.get_unchecked(i.as_vec_ref())
    }
}

impl<V: AsReference<Vec2>, T: Clone + Default + Sized> IndexMut<V> for Rect<T> {
    #[inline]
    fn index_mut(&mut self, i: V) -> &mut Self::Output {
        self.get_mut_unchecked(i.as_vec_ref())
    }
}

#[cfg(test)]
mod test {
    use crate::rect::Rect;

    #[test]
    fn test_index() {
        let r: Rect<bool> = Rect::new((10, 10), false);
        assert_eq!(r[&(0, 1)], false);
        assert_eq!(r[(0, 1)], false);
    }

    #[test]
    fn test_index_mut() {
        let mut r: Rect<bool> = Rect::new((10, 10), false);
        r[&(1, 1)] = true;
        assert_eq!(r[&(1, 1)], true);
        r[(2, 2)] = true;
        assert_eq!(r[(2, 2)], true);
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
