//! misc functions about 2D/3D computation
use serde::Serialize;

pub trait GeometricMath {
    type BaseType;
    type Vector;
    fn add<V: AsVecReference<Self>>(&self, other: V) -> Self
    where
        Self: Sized;
    fn sub<V: AsVecReference<Self>>(&self, other: V) -> Self
    where
        Self: Sized;
    fn manhattan_distance<V: AsVecReference<Self>>(&self, other: V) -> isize
    where
        Self: Sized;
    fn add_scalar(&self, other: Self::BaseType) -> Self;
    fn mul_scalar(&self, other: Self::BaseType) -> Self;
    fn included<V1: AsVecReference<Self>, V2: AsVecReference<Self>>(
        &self,
        from: V1,
        to: V2,
    ) -> Option<&Self>
    where
        Self: Sized;
    fn shift(&self, vec: &Self::Vector) -> Option<Self>
    where
        Self: Sized;
    fn scale(&self, s: Self::BaseType) -> Self;
}

pub trait GeometricRotation {
    fn turn_right(&self) -> Self;
    fn turn_left(&self) -> Self;
}

pub type Dim2<L> = (L, L);
pub type Vec2 = (isize, isize);

pub trait AsVecReference<V> {
    fn as_vec_ref(&self) -> &V;
}

impl<L> AsVecReference<Dim2<L>> for Dim2<L> {
    #[inline]
    fn as_vec_ref(&self) -> &Dim2<L> {
        self
    }
}

impl<L> AsVecReference<Dim2<L>> for &Dim2<L> {
    #[inline]
    fn as_vec_ref(&self) -> &Dim2<L> {
        self
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub enum Direction {
    #[default]
    NORTH,
    EAST,
    SOUTH,
    WEST,
}

pub const DIRECTIONS: [Direction; 4] = [
    Direction::NORTH,
    Direction::EAST,
    Direction::SOUTH,
    Direction::WEST,
];

impl Direction {
    pub fn as_vec2(&self) -> Vec2 {
        match self {
            Direction::NORTH => (-1, 0),
            Direction::EAST => (0, 1),
            Direction::SOUTH => (1, 0),
            Direction::WEST => (0, -1),
        }
    }
    pub fn from_vec2(vec: &Vec2) -> Option<Self> {
        match vec {
            (0, -1) => Some(Direction::NORTH),
            (-1, 0) => Some(Direction::EAST),
            (0, 1) => Some(Direction::SOUTH),
            (1, 0) => Some(Direction::WEST),
            _ => None,
        }
    }
    pub fn as_char(&self) -> char {
        match self {
            Direction::NORTH => '^',
            Direction::EAST => '>',
            Direction::SOUTH => 'v',
            Direction::WEST => '<',
        }
    }
}

impl GeometricRotation for Direction {
    fn turn_right(&self) -> Self {
        match self {
            Direction::NORTH => Direction::EAST,
            Direction::EAST => Direction::SOUTH,
            Direction::SOUTH => Direction::WEST,
            Direction::WEST => Direction::NORTH,
        }
    }
    fn turn_left(&self) -> Self {
        match self {
            Direction::EAST => Direction::NORTH,
            Direction::SOUTH => Direction::EAST,
            Direction::WEST => Direction::SOUTH,
            Direction::NORTH => Direction::WEST,
        }
    }
}

pub const DIR4: [Vec2; 4] = [(-1, 0), (0, 1), (1, 0), (0, -1)];

pub const DIR8: [Vec2; 8] = [
    (-1, 0),
    (-1, 1),
    (0, 1),
    (1, 1),
    (1, 0),
    (1, -1),
    (0, -1),
    (-1, -1),
];

impl GeometricRotation for Vec2 {
    fn turn_right(&self) -> Self {
        match self {
            (0, 1) => (1, 0),
            (1, 0) => (0, -1),
            (0, -1) => (-1, 0),
            (-1, 0) => (0, 1),
            _ => unreachable!(),
        }
    }
    fn turn_left(&self) -> Self {
        match self {
            (0, 1) => (-1, 0),
            (1, 0) => (0, 1),
            (0, -1) => (1, 0),
            (-1, 0) => (0, -1),
            _ => unreachable!(),
        }
    }
}

impl GeometricMath for Dim2<isize> {
    type BaseType = isize;
    type Vector = Vec2;
    fn add<V: AsVecReference<Self>>(&self, other: V) -> Self
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0 + o.0, self.1 + o.1)
    }
    fn sub<V: AsVecReference<Self>>(&self, other: V) -> Self
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0 - o.0, self.1 - o.1)
    }
    fn manhattan_distance<V: AsVecReference<Self>>(&self, other: V) -> isize
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0.abs_diff(o.0) + self.1.abs_diff(o.1)) as isize
    }
    fn add_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 + other, self.1 + other)
    }
    fn mul_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 * other, self.1 * other)
    }
    fn included<V1: AsVecReference<Self>, V2: AsVecReference<Self>>(
        &self,
        from: V1,
        to: V2,
    ) -> Option<&Self>
    where
        Self: Sized,
    {
        let f = from.as_vec_ref();
        let t = to.as_vec_ref();
        (f.0 <= self.0 && self.0 < t.0 && f.1 <= self.1 && self.1 < t.1).then_some(self)
    }
    fn shift(&self, vec: &Vec2) -> Option<Self>
    where
        Self: Sized,
    {
        Some((self.0 + vec.0, self.1 + vec.1))
    }
    fn scale(&self, k: Self::BaseType) -> Self {
        (self.0 * k, self.1 * k)
    }
}

impl GeometricMath for Dim2<usize> {
    type BaseType = usize;
    type Vector = Vec2;
    fn add<V: AsVecReference<Self>>(&self, other: V) -> Self
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0 + o.0, self.1 + o.1)
    }
    fn sub<V: AsVecReference<Self>>(&self, other: V) -> Self
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0.saturating_sub(o.0), self.1.saturating_sub(o.1))
    }
    fn manhattan_distance<V: AsVecReference<Self>>(&self, other: V) -> isize
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0.abs_diff(o.0) + self.1.abs_diff(o.1)) as isize
    }
    fn add_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 + other, self.1 + other)
    }
    fn mul_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 * other, self.1 * other)
    }
    fn included<V1: AsVecReference<Self>, V2: AsVecReference<Self>>(
        &self,
        from: V1,
        to: V2,
    ) -> Option<&Self>
    where
        Self: Sized,
    {
        let f = from.as_vec_ref();
        let t = to.as_vec_ref();
        (f.0 <= self.0 && self.0 < t.0 && f.1 <= self.1 && self.1 < t.1).then_some(self)
    }
    fn shift(&self, vec: &Vec2) -> Option<Self>
    where
        Self: Sized,
    {
        let t = self.0 as isize + vec.0;
        let u = self.1 as isize + vec.1;
        (0 <= t && 0 <= u).then_some((t as usize, u as usize))
    }
    fn scale(&self, k: Self::BaseType) -> Self {
        (self.0 * k, self.1 * k)
    }
}

pub type Dim3<L> = (L, L, L);
pub type Vec3 = (isize, isize, isize);

impl<L> AsVecReference<Dim3<L>> for Dim3<L> {
    #[inline]
    fn as_vec_ref(&self) -> &Dim3<L> {
        self
    }
}

impl<L> AsVecReference<Dim3<L>> for &Dim3<L> {
    #[inline]
    fn as_vec_ref(&self) -> &Dim3<L> {
        self
    }
}

const _DIR26: [Vec3; 26] = [
    // (0, 0, 0),
    (0, 0, -1),
    (0, 0, 1),
    (0, -1, 0),
    (0, -1, -1),
    (0, -1, 1),
    (0, 1, 0),
    (0, 1, -1),
    (0, 1, 1),
    (-1, 0, 0),
    (-1, 0, -1),
    (-1, 0, 1),
    (-1, -1, 0),
    (-1, -1, -1),
    (-1, -1, 1),
    (-1, 1, 0),
    (-1, 1, -1),
    (-1, 1, 1),
    (1, 0, 0),
    (1, 0, -1),
    (1, 0, 1),
    (1, -1, 0),
    (1, -1, -1),
    (1, -1, 1),
    (1, 1, 0),
    (1, 1, -1),
    (1, 1, 1),
];

impl GeometricMath for Dim3<isize> {
    type BaseType = isize;
    type Vector = Vec3;
    fn add<V: AsVecReference<Self>>(&self, other: V) -> Self
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0 + o.0, self.1 + o.1, self.2 + o.2)
    }
    fn sub<V: AsVecReference<Self>>(&self, other: V) -> Self
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0 - o.0, self.1 - o.1, self.2 - o.2)
    }
    fn manhattan_distance<V: AsVecReference<Self>>(&self, other: V) -> isize
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0.abs_diff(o.0) + self.1.abs_diff(o.1) + self.2.abs_diff(o.2)) as isize
    }
    fn add_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 + other, self.1 + other, self.2 + other)
    }
    fn mul_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 * other, self.1 * other, self.2 * other)
    }
    fn included<V1: AsVecReference<Self>, V2: AsVecReference<Self>>(
        &self,
        from: V1,
        to: V2,
    ) -> Option<&Self>
    where
        Self: Sized,
    {
        let f = from.as_vec_ref();
        let t = to.as_vec_ref();
        (f.0 <= self.0
            && self.0 < t.0
            && f.1 <= self.1
            && self.1 < t.1
            && f.2 <= self.2
            && self.2 < t.2)
            .then_some(self)
    }
    fn shift(&self, vec: &Self::Vector) -> Option<Self>
    where
        Self: Sized,
    {
        Some((self.0 + vec.0, self.1 + vec.1, self.2 + vec.2))
    }
    fn scale(&self, k: Self::BaseType) -> Self {
        (self.0 * k, self.1 * k, self.2 * k)
    }
}

impl GeometricMath for Dim3<usize> {
    type BaseType = usize;
    type Vector = Vec3;
    fn add<V: AsVecReference<Self>>(&self, other: V) -> Self
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0 + o.0, self.1 + o.1, self.2 + o.2)
    }
    fn sub<V: AsVecReference<Self>>(&self, other: V) -> Self
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (
            self.0.saturating_sub(o.0),
            self.1.saturating_sub(o.1),
            self.2.saturating_sub(o.2),
        )
    }
    fn manhattan_distance<V: AsVecReference<Self>>(&self, other: V) -> isize
    where
        Self: Sized,
    {
        let o = other.as_vec_ref();
        (self.0.abs_diff(o.0) + self.1.abs_diff(o.1) + self.2.abs_diff(o.2)) as isize
    }
    fn add_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 + other, self.1 + other, self.2 + other)
    }
    fn mul_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 * other, self.1 * other, self.2 * other)
    }
    fn included<V1: AsVecReference<Self>, V2: AsVecReference<Self>>(
        &self,
        from: V1,
        to: V2,
    ) -> Option<&Self>
    where
        Self: Sized,
    {
        let f = from.as_vec_ref();
        let t = to.as_vec_ref();
        (f.0 <= self.0
            && self.0 < t.0
            && f.1 <= self.1
            && self.1 < t.1
            && f.2 <= self.2
            && self.2 < t.2)
            .then_some(self)
    }
    fn shift(&self, vec: &Self::Vector) -> Option<Self>
    where
        Self: Sized,
    {
        let t = self.0 as isize + vec.0;
        let u = self.1 as isize + vec.1;
        let v = self.1 as isize + vec.2;
        (0 <= t && 0 <= u && 0 <= v).then_some((t as usize, u as usize, v as usize))
    }
    fn scale(&self, k: Self::BaseType) -> Self {
        (self.0 * k, self.1 * k, self.2 * k)
    }
}

/// returns `[self - 1, self, self + 1]`
/// ```
/// use adventofcode::geometric;
/// assert_eq!(geometric::neighbors(0, 1), [None, Some(0), None]);
/// assert_eq!(geometric::neighbors(0, 2), [None, Some(0), Some(1)]);
/// assert_eq!(geometric::neighbors(1, 1), [Some(0), None, None]);
/// assert_eq!(geometric::neighbors(1, 3), [Some(0), Some(1), Some(2)]);
pub fn neighbors(here: usize, upto: usize) -> [Option<usize>; 3] {
    [
        here.checked_sub(1),
        (here < upto).then_some(here),
        (here + 1 < upto).then_some(here + 1),
    ]
}

/// returns all 26 neighbors in 3D space
// pub fn cubic_neighbors26(
//     x: usize,
//     y: usize,
//     z: usize,
//     bx: usize,
//     by: usize,
//     bz: usize,
// ) -> Vec<(usize, usize, usize)> {
//     neighbors(x, bx)
//         .iter()
//         .filter(|s| s.is_some())
//         .flat_map(|xx| {
//             neighbors(y, by)
//                 .iter()
//                 .filter(|t| t.is_some())
//                 .flat_map(|yy| {
//                     neighbors(z, bz)
//                         .iter()
//                         .filter(|t| t.is_some())
//                         .map(|zz| (xx.unwrap(), yy.unwrap(), zz.unwrap()))
//                         .filter(|(xx, yy, zz)| !(*xx == x && *yy == y && *zz == z))
//                         .collect::<Vec<_>>()
//                 })
//                 .collect::<Vec<_>>()
//         })
//         .collect::<Vec<_>>()
// }

pub trait GeometricAddition {
    fn move_to(&self, q: Dim2<isize>, h: usize, w: usize) -> Option<Box<Self>>;
}

impl GeometricAddition for Dim2<usize> {
    fn move_to(&self, d: Dim2<isize>, h: usize, w: usize) -> Option<Box<Dim2<usize>>> {
        let y = self.0 as isize + d.0;
        let x = self.1 as isize + d.1;
        (0 <= y && y < h as isize && 0 <= x && x < w as isize)
            .then(|| Box::new((y as usize, x as usize)))
    }
}

impl GeometricAddition for Dim2<isize> {
    fn move_to(&self, d: Dim2<isize>, h: usize, w: usize) -> Option<Box<Dim2<isize>>> {
        let y = self.0 + d.0;
        let x = self.1 + d.1;
        (0 <= y && y < h as isize && 0 <= x && x < w as isize).then(|| Box::new((y, x)))
    }
}

pub struct Dim2Iter1<'a, T, const N: u8> {
    base: &'a Dim2<T>,
    boundary: &'a Dim2<T>,
    index: u8,
}

pub struct Dim2Iter2<'a, T, const N: u8> {
    base: &'a Dim2<T>,
    boundary0: &'a Dim2<T>,
    boundary1: &'a Dim2<T>,
    index: u8,
}

pub struct Dim3Iter1<'a, T, const N: u8> {
    base: &'a Dim3<T>,
    boundary: &'a Dim3<T>,
    index: u8,
}

pub trait NeighborIter<T> {
    /// Iterate on its 4 neighbors. Their positions are in [(0, 0), `boundary1`).
    fn iter4<'a>(&'a self, boundary: &'a Dim2<T>) -> Dim2Iter1<'a, T, 4>;
    /// Iterate on its 4 neighbors on 3Dim space.
    /// Their positions are in [(0, 0, 0), `boundary1`).
    fn iter6<'a>(&'a self, boundary: &'a Dim3<T>) -> Dim3Iter1<'a, T, 6>;
    /// Iterate on its 8 neighbors. Their positions are in [(0, 0), `boundary1`).
    fn iter8<'a>(&'a self, boundary: &'a Dim2<T>) -> Dim2Iter1<'a, T, 8>;
    /// Iterate on its 8 neighbors. Their positions are in [`boundary0`, `boundary1`).
    fn iter8_from<'a>(
        &'a self,
        boundary0: &'a Dim2<T>,
        boundary1: &'a Dim2<T>,
    ) -> Dim2Iter2<'a, T, 8>;
    /// Iterate on its 8 neighbors and itself. Their positions are in [(0, 0), `boundary1`).
    fn iter9<'a>(&'a self, boundary: &'a Dim2<T>) -> Dim2Iter1<'a, T, 9>;
}

impl NeighborIter<usize> for Dim2<usize> {
    fn iter4<'a>(&'a self, boundary: &'a Dim2<usize>) -> Dim2Iter1<'a, usize, 4> {
        Dim2Iter1 {
            base: self,
            boundary,
            index: 0,
        }
    }
    fn iter6<'a>(&'a self, _: &'a Dim3<usize>) -> Dim3Iter1<'a, usize, 6> {
        unimplemented!()
    }
    fn iter8<'a>(&'a self, boundary: &'a Dim2<usize>) -> Dim2Iter1<'a, usize, 8> {
        Dim2Iter1 {
            base: self,
            boundary,
            index: 0,
        }
    }
    fn iter8_from<'a>(
        &'a self,
        boundary0: &'a Dim2<usize>,
        boundary1: &'a Dim2<usize>,
    ) -> Dim2Iter2<'a, usize, 8> {
        Dim2Iter2 {
            base: self,
            boundary0,
            boundary1,
            index: 0,
        }
    }
    fn iter9<'a>(&'a self, boundary: &'a Dim2<usize>) -> Dim2Iter1<'a, usize, 9> {
        Dim2Iter1 {
            base: self,
            boundary,
            index: 0,
        }
    }
}

impl<'a> Iterator for Dim2Iter1<'a, usize, 4> {
    type Item = Dim2<usize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < 4 {
            self.index += 1;
            match self.index {
                1 if 0 < self.base.0 => return Some((self.base.0 - 1, self.base.1)),
                2 if 0 < self.base.1 => return Some((self.base.0, self.base.1 - 1)),
                3 if self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0, self.base.1 + 1));
                }
                4 if self.base.0 + 1 < self.boundary.0 => {
                    return Some((self.base.0 + 1, self.base.1));
                }
                _ => (),
            }
        }
        None
    }
}

impl<'a> Iterator for Dim2Iter1<'a, usize, 8> {
    type Item = Dim2<usize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < 8 {
            self.index += 1;
            match self.index {
                1 if 0 < self.base.0 && 0 < self.base.1 => {
                    return Some((self.base.0 - 1, self.base.1 - 1));
                }
                2 if 0 < self.base.0 => return Some((self.base.0 - 1, self.base.1)),
                3 if 0 < self.base.0 && self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0 - 1, self.base.1 + 1));
                }
                4 if 0 < self.base.1 => return Some((self.base.0, self.base.1 - 1)),
                5 if self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0, self.base.1 + 1));
                }
                6 if self.base.0 + 1 < self.boundary.0 && 0 < self.base.1 => {
                    return Some((self.base.0 + 1, self.base.1 - 1));
                }
                7 if self.base.0 + 1 < self.boundary.0 => {
                    return Some((self.base.0 + 1, self.base.1));
                }
                8 if self.base.0 + 1 < self.boundary.0 && self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0 + 1, self.base.1 + 1));
                }
                _ => (),
            }
        }
        None
    }
}

impl<'a> Iterator for Dim2Iter1<'a, usize, 9> {
    type Item = Dim2<usize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < 9 {
            self.index += 1;
            match self.index {
                1 if 0 < self.base.0 && 0 < self.base.1 => {
                    return Some((self.base.0 - 1, self.base.1 - 1));
                }
                2 if 0 < self.base.0 => return Some((self.base.0 - 1, self.base.1)),
                3 if 0 < self.base.0 && self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0 - 1, self.base.1 + 1));
                }
                4 if 0 < self.base.1 => return Some((self.base.0, self.base.1 - 1)),
                5 => return Some((self.base.0, self.base.1)),
                6 if self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0, self.base.1 + 1));
                }
                7 if self.base.0 + 1 < self.boundary.0 && 0 < self.base.1 => {
                    return Some((self.base.0 + 1, self.base.1 - 1));
                }
                8 if self.base.0 + 1 < self.boundary.0 => {
                    return Some((self.base.0 + 1, self.base.1));
                }
                9 if self.base.0 + 1 < self.boundary.0 && self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0 + 1, self.base.1 + 1));
                }
                _ => (),
            }
        }
        None
    }
}

impl<'a> Iterator for Dim2Iter2<'a, usize, 8> {
    type Item = Dim2<usize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < 8 {
            self.index += 1;
            match self.index {
                1 if self.boundary0.0 < self.base.0 && self.boundary0.1 < self.base.1 => {
                    return Some((self.base.0 - 1, self.base.1 - 1));
                }
                2 if self.boundary0.0 < self.base.0 => return Some((self.base.0 - 1, self.base.1)),
                3 if self.boundary0.0 < self.base.0 && self.base.1 + 1 < self.boundary1.1 => {
                    return Some((self.base.0 - 1, self.base.1 + 1));
                }
                4 if self.boundary0.1 < self.base.1 => return Some((self.base.0, self.base.1 - 1)),
                5 if self.base.1 + 1 < self.boundary1.1 => {
                    return Some((self.base.0, self.base.1 + 1));
                }
                6 if self.base.0 + 1 < self.boundary1.0 && self.boundary0.1 < self.base.1 => {
                    return Some((self.base.0 + 1, self.base.1 - 1));
                }
                7 if self.base.0 + 1 < self.boundary1.0 => {
                    return Some((self.base.0 + 1, self.base.1));
                }
                8 if self.base.0 + 1 < self.boundary1.0 && self.base.1 + 1 < self.boundary1.1 => {
                    return Some((self.base.0 + 1, self.base.1 + 1));
                }
                _ => (),
            }
        }
        None
    }
}

impl NeighborIter<isize> for Dim2<isize> {
    fn iter4<'a>(&'a self, boundary: &'a Dim2<isize>) -> Dim2Iter1<'a, isize, 4> {
        Dim2Iter1 {
            base: self,
            boundary,
            index: 0,
        }
    }
    fn iter6<'a>(&'a self, _: &'a Dim3<isize>) -> Dim3Iter1<'a, isize, 6> {
        unimplemented!()
    }
    fn iter8<'a>(&'a self, boundary: &'a Dim2<isize>) -> Dim2Iter1<'a, isize, 8> {
        Dim2Iter1 {
            base: self,
            boundary,
            index: 0,
        }
    }
    fn iter8_from<'a>(
        &'a self,
        boundary0: &'a Dim2<isize>,
        boundary1: &'a Dim2<isize>,
    ) -> Dim2Iter2<'a, isize, 8> {
        Dim2Iter2 {
            base: self,
            boundary0,
            boundary1,
            index: 0,
        }
    }
    fn iter9<'a>(&'a self, boundary: &'a Dim2<isize>) -> Dim2Iter1<'a, isize, 9> {
        Dim2Iter1 {
            base: self,
            boundary,
            index: 0,
        }
    }
}

impl<'a> Iterator for Dim2Iter1<'a, isize, 4> {
    type Item = Dim2<isize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < 4 {
            self.index += 1;
            match self.index {
                1 if 0 < self.base.0 => return Some((self.base.0 - 1, self.base.1)),
                2 if 0 < self.base.1 => return Some((self.base.0, self.base.1 - 1)),
                3 if self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0, self.base.1 + 1));
                }
                4 if self.base.0 + 1 < self.boundary.0 => {
                    return Some((self.base.0 + 1, self.base.1));
                }
                _ => (),
            }
        }
        None
    }
}

impl<'a> Iterator for Dim2Iter1<'a, isize, 8> {
    type Item = Dim2<isize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < 8 {
            self.index += 1;
            match self.index {
                1 if 0 < self.base.0 && 0 < self.base.1 => {
                    return Some((self.base.0 - 1, self.base.1 - 1));
                }
                2 if 0 < self.base.0 => return Some((self.base.0 - 1, self.base.1)),
                3 if 0 < self.base.0 && self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0 - 1, self.base.1 + 1));
                }
                4 if 0 < self.base.1 => return Some((self.base.0, self.base.1 - 1)),
                5 if self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0, self.base.1 + 1));
                }
                6 if self.base.0 + 1 < self.boundary.0 && 0 < self.base.1 => {
                    return Some((self.base.0 + 1, self.base.1 - 1));
                }
                7 if self.base.0 + 1 < self.boundary.0 => {
                    return Some((self.base.0 + 1, self.base.1));
                }
                8 if self.base.0 + 1 < self.boundary.0 && self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0 + 1, self.base.1 + 1));
                }
                _ => (),
            }
        }
        None
    }
}

impl<'a> Iterator for Dim2Iter1<'a, isize, 9> {
    type Item = Dim2<isize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < 9 {
            self.index += 1;
            match self.index {
                1 if 0 < self.base.0 && 0 < self.base.1 => {
                    return Some((self.base.0 - 1, self.base.1 - 1));
                }
                2 if 0 < self.base.0 => return Some((self.base.0 - 1, self.base.1)),
                3 if 0 < self.base.0 && self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0 - 1, self.base.1 + 1));
                }
                4 if 0 < self.base.1 => return Some((self.base.0, self.base.1 - 1)),
                5 => return Some((self.base.0, self.base.1)),
                6 if self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0, self.base.1 + 1));
                }
                7 if self.base.0 + 1 < self.boundary.0 && 0 < self.base.1 => {
                    return Some((self.base.0 + 1, self.base.1 - 1));
                }
                8 if self.base.0 + 1 < self.boundary.0 => {
                    return Some((self.base.0 + 1, self.base.1));
                }
                9 if self.base.0 + 1 < self.boundary.0 && self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0 + 1, self.base.1 + 1));
                }
                _ => (),
            }
        }
        None
    }
}

impl<'a> Iterator for Dim2Iter2<'a, isize, 8> {
    type Item = Dim2<isize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < 8 {
            self.index += 1;
            match self.index {
                1 if self.boundary0.0 < self.base.0 && self.boundary0.1 < self.base.1 => {
                    return Some((self.base.0 - 1, self.base.1 - 1));
                }
                2 if self.boundary0.0 < self.base.0 => return Some((self.base.0 - 1, self.base.1)),
                3 if self.boundary0.0 < self.base.0 && self.base.1 + 1 < self.boundary1.1 => {
                    return Some((self.base.0 - 1, self.base.1 + 1));
                }
                4 if self.boundary0.1 < self.base.1 => return Some((self.base.0, self.base.1 - 1)),
                5 if self.base.1 + 1 < self.boundary1.1 => {
                    return Some((self.base.0, self.base.1 + 1));
                }
                6 if self.base.0 + 1 < self.boundary1.0 && self.boundary0.1 < self.base.1 => {
                    return Some((self.base.0 + 1, self.base.1 - 1));
                }
                7 if self.base.0 + 1 < self.boundary1.0 => {
                    return Some((self.base.0 + 1, self.base.1));
                }
                8 if self.base.0 + 1 < self.boundary1.0 && self.base.1 + 1 < self.boundary1.1 => {
                    return Some((self.base.0 + 1, self.base.1 + 1));
                }
                _ => (),
            }
        }
        None
    }
}

impl NeighborIter<usize> for Dim3<usize> {
    fn iter4<'a>(&'a self, _: &'a Dim2<usize>) -> Dim2Iter1<'a, usize, 4> {
        unimplemented!()
    }
    fn iter6<'a>(&'a self, boundary: &'a Dim3<usize>) -> Dim3Iter1<'a, usize, 6> {
        Dim3Iter1 {
            base: self,
            boundary,
            index: 0,
        }
    }
    fn iter8<'a>(&'a self, _: &'a Dim2<usize>) -> Dim2Iter1<'a, usize, 8> {
        unimplemented!()
    }
    fn iter8_from<'a>(&'a self, _: &'a Dim2<usize>, _: &'a Dim2<usize>) -> Dim2Iter2<'a, usize, 8> {
        unimplemented!()
    }
    fn iter9<'a>(&'a self, _: &'a Dim2<usize>) -> Dim2Iter1<'a, usize, 9> {
        unimplemented!()
    }
}

impl<'a> Iterator for Dim3Iter1<'a, usize, 6> {
    type Item = Dim3<usize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < 6 {
            self.index += 1;
            match self.index {
                1 if 0 < self.base.0 => {
                    return Some((self.base.0 - 1, self.base.1 - 1, self.base.2));
                }
                2 if 0 < self.base.1 => return Some((self.base.0, self.base.1 - 1, self.base.2)),
                3 if 0 < self.base.2 => return Some((self.base.0, self.base.1, self.base.2 - 1)),
                4 if self.base.2 + 1 < self.boundary.2 => {
                    return Some((self.base.0, self.base.1, self.base.2 + 1));
                }
                5 if self.base.1 + 1 < self.boundary.1 => {
                    return Some((self.base.0, self.base.1 + 1, self.base.2));
                }
                6 if self.base.0 + 1 < self.boundary.0 => {
                    return Some((self.base.0 + 1, self.base.1, self.base.2));
                }
                _ => (),
            }
        }
        None
    }
}
