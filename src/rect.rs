use crate::geometric::*;

/// A struct representing a rectangle with elements of type `T`.
///
/// # Examples
///
/// ```
/// use your_crate::geometry::{Vec2, Rect};
///
/// let rect = Rect::new((3.0, 4.0), "Hello");
/// assert_eq!(rect.get(&(1.0, 2.0)), Some(&"Hello"));
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
    pub fn get(&self, index: &Vec2) -> Option<&T> {
        self.to_index(index).and_then(|i| self.vec.get(i))
    }
    pub fn set(&mut self, index: &Vec2, val: T) {
        if let Some(i) = self.to_index(index) {
            self.vec[i] = val;
        }
    }
    pub fn to_index(&self, index: &Vec2) -> Option<usize> {
        if (0..self.size.0).contains(&index.0) && (0..self.size.1).contains(&index.1) {
            Some((index.0 * index.1) as usize)
        } else {
            None
        }
    }
}
