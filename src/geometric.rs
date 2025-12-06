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
    fn neighbors(&self, boundary: Option<Self>) -> Vec<Self>
    where
        Self: Sized;
    fn neighbors2(&self, boundary: Option<Self>) -> Vec<Self>
    where
        Self: Sized;
    fn neighbors4<V1: AsVecReference<Self>, V2: AsVecReference<Self>>(
        &self,
        boundary0: V1,
        boundary1: V2,
    ) -> Vec<Self>
    where
        Self: Sized;
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
    fn neighbors(&self, boundary: Option<Self>) -> Vec<Self>
    where
        Self: Sized,
    {
        let b0 = boundary.map_or(isize::MAX, |v| v.0.abs());
        let b1 = boundary.map_or(isize::MAX, |v| v.1.abs());
        DIR4.iter()
            .filter_map(|d| self.shift(d))
            .filter(|v| v.0.abs() < b0 && v.1.abs() < b1)
            .collect::<Vec<Self>>()
    }
    fn neighbors2(&self, boundary: Option<Self>) -> Vec<Self>
    where
        Self: Sized,
    {
        let b0 = boundary.map_or(isize::MAX, |v| v.0.abs());
        let b1 = boundary.map_or(isize::MAX, |v| v.1.abs());
        DIR8.iter()
            .filter_map(|d| self.shift(d))
            .filter(|v| v.0.abs() < b0 && v.1.abs() < b1)
            .collect::<Vec<Self>>()
    }
    fn neighbors4<V1: AsVecReference<Dim2<isize>>, V2: AsVecReference<Dim2<isize>>>(
        &self,
        boundary0: V1,
        boundary1: V2,
    ) -> Vec<Self> {
        let b0 = boundary0.as_vec_ref();
        let b1 = boundary1.as_vec_ref();
        [self.0 - 1, self.0, self.0 + 1]
            .iter()
            .filter(|s| b0.0 <= **s && **s < b1.0)
            .flat_map(|y| {
                [self.1 - 1, self.1, self.1 + 1]
                    .iter()
                    .filter(|t| b0.1 <= **t && **t < b1.1)
                    .filter(|x| *y == self.0 || **x == self.1)
                    .filter(|x| *y != self.0 || **x != self.1)
                    .map(|x| (*y, *x))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
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
    fn neighbors(&self, boundary: Option<Self>) -> Vec<Self>
    where
        Self: Sized,
    {
        let b0 = boundary.map_or(usize::MAX, |v| v.0);
        let b1 = boundary.map_or(usize::MAX, |v| v.1);
        DIR4.iter()
            .filter_map(|d| self.shift(d))
            .filter(|v| v.0 < b0 && v.1 < b1)
            .collect::<Vec<Self>>()
    }
    fn neighbors2(&self, boundary: Option<Self>) -> Vec<Self>
    where
        Self: Sized,
    {
        let b0 = boundary.map_or(usize::MAX, |v| v.0);
        let b1 = boundary.map_or(usize::MAX, |v| v.1);
        DIR8.iter()
            .filter_map(|d| self.shift(d))
            .filter(|v| v.0 < b0 && v.1 < b1)
            .collect::<Vec<Self>>()
    }
    fn neighbors4<V1: AsVecReference<Dim2<usize>>, V2: AsVecReference<Dim2<usize>>>(
        &self,
        boundary0: V1,
        boundary1: V2,
    ) -> Vec<Self> {
        let b0 = boundary0.as_vec_ref();
        let b1 = boundary1.as_vec_ref();
        (0.max(self.0 as isize - 1) as usize..=self.0 + 1)
            .filter(|s| b0.0 <= *s && *s < b1.0)
            .flat_map(|y| {
                (0.max(self.1 as isize - 1) as usize..=self.1 + 1)
                    .filter(|t| b0.1 <= *t && *t < b1.1)
                    .filter(|x| y == self.0 || *x == self.1)
                    .filter(|x| y != self.0 || *x != self.1)
                    .map(|x| (y, x))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
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

const DIR6: [Vec3; 6] = [
    (-1, 0, 0),
    (1, 0, 0),
    (0, -1, 0),
    (0, 1, 0),
    (0, 0, -1),
    (0, 0, 1),
];

const DIR26: [Vec3; 26] = [
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
    fn neighbors(&self, boundary: Option<Self>) -> Vec<Self>
    where
        Self: Sized,
    {
        let b0 = boundary.map_or(isize::MAX, |v| v.0.abs());
        let b1 = boundary.map_or(isize::MAX, |v| v.1.abs());
        let b2 = boundary.map_or(isize::MAX, |v| v.2.abs());
        DIR6.iter()
            .filter_map(|d| self.shift(d))
            .filter(|v| v.0.abs() < b0 && v.1.abs() < b1 && v.2.abs() < b2)
            .collect::<Vec<Self>>()
    }
    fn neighbors2(&self, boundary: Option<Self>) -> Vec<Self>
    where
        Self: Sized,
    {
        let b0 = boundary.map_or(isize::MAX, |v| v.0.abs());
        let b1 = boundary.map_or(isize::MAX, |v| v.1.abs());
        let b2 = boundary.map_or(isize::MAX, |v| v.2.abs());
        DIR26
            .iter()
            .filter_map(|d| self.shift(d))
            .filter(|v| v.0.abs() < b0 && v.1.abs() < b1 && v.2.abs() < b2)
            .collect::<Vec<Self>>()
    }
    fn neighbors4<V1: AsVecReference<Dim3<isize>>, V2: AsVecReference<Dim3<isize>>>(
        &self,
        _boundary0: V1,
        _boundary1: V2,
    ) -> Vec<Self> {
        unimplemented!()
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
    fn neighbors(&self, boundary: Option<Self>) -> Vec<Self>
    where
        Self: Sized,
    {
        let b0 = boundary.map_or(usize::MAX, |v| v.0);
        let b1 = boundary.map_or(usize::MAX, |v| v.1);
        let b2 = boundary.map_or(usize::MAX, |v| v.2);
        DIR6.iter()
            .filter_map(|d| self.shift(d))
            .filter(|v| v.0 < b0 && v.1 < b1 && v.2 < b2)
            .collect::<Vec<Self>>()
    }
    fn neighbors2(&self, boundary: Option<Self>) -> Vec<Self>
    where
        Self: Sized,
    {
        let b0 = boundary.map_or(usize::MAX, |v| v.0);
        let b1 = boundary.map_or(usize::MAX, |v| v.1);
        let b2 = boundary.map_or(usize::MAX, |v| v.2);
        DIR26
            .iter()
            .filter_map(|d| self.shift(d))
            .filter(|v| v.0 < b0 && v.1 < b1 && v.2 < b2)
            .collect::<Vec<Self>>()
    }
    fn neighbors4<V1: AsVecReference<Dim3<usize>>, V2: AsVecReference<Dim3<usize>>>(
        &self,
        _boundary0: V1,
        _boundary1: V2,
    ) -> Vec<Self> {
        unimplemented!()
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

/// returns all 4 neighbors
/// ```
/// use adventofcode::geometric;
/// assert_eq!(geometric::neighbors4(0, 0, 2, 2), vec![(0, 1), (1, 0)]);
/// assert_eq!(geometric::neighbors4(1, 1, 3, 3), vec![(0, 1), (1, 0), (1, 2), (2, 1)]);
/// assert_eq!(geometric::neighbors4(1, 1, 2, 3), vec![(0, 1), (1, 0), (1, 2)]);
/// assert_eq!(geometric::neighbors4(1, 0, 3, 3), vec![(0, 0), (1, 1), (2, 0)]);
/// assert_eq!(geometric::neighbors4(1, 0, 3, 2), vec![(0, 0), (1, 1), (2, 0)]);
/// assert_eq!(geometric::neighbors4(3, 3, 3, 3), vec![]);
/// ```
pub fn neighbors4(j: usize, i: usize, height: usize, width: usize) -> Vec<(usize, usize)> {
    neighbors(j, height)
        .iter()
        .filter(|s| s.is_some())
        .flat_map(|jj| {
            neighbors(i, width)
                .iter()
                .filter(|t| t.is_some())
                .map(|ii| (jj.unwrap(), ii.unwrap()))
                .collect::<Vec<_>>()
        })
        .filter(|(jj, ii)| (*jj == j || *ii == i) && !(*jj == j && *ii == i))
        .collect::<Vec<_>>()
}

/// returns all 9 neighbors
/// ```
/// use adventofcode::geometric;
/// assert_eq!(geometric::neighbors9(1, 1, 3, 3).len(), 9);
/// assert_eq!(geometric::neighbors9(1, 1, 3, 3), vec![(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]);
/// assert_eq!(geometric::neighbors9(0, 0, 3, 3), vec![(0,0), (0,1), (1,0), (1,1)]);
/// ```
pub fn neighbors9(j: usize, i: usize, height: usize, width: usize) -> Vec<(usize, usize)> {
    neighbors(j, height)
        .iter()
        .filter(|s| s.is_some())
        .flat_map(|jj| {
            neighbors(i, width)
                .iter()
                .filter(|t| t.is_some())
                .map(|ii| (jj.unwrap(), ii.unwrap()))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
}

/// returns all 6 neighbors in 3D space
/// ```
/// use adventofcode::geometric;
/// let mut a = geometric::cubic_neighbors6(1, 1, 1, 3, 3, 3);
/// a.sort();
/// let mut b = vec![(1,1,0), (1,1,2), (1,0,1), (1,2,1), (0,1,1), (2,1,1)];
/// b.sort();
/// assert_eq!(a, b);
/// ```
#[allow(clippy::nonminimal_bool)]
pub fn cubic_neighbors6(
    x: usize,
    y: usize,
    z: usize,
    bx: usize,
    by: usize,
    bz: usize,
) -> Vec<(usize, usize, usize)> {
    neighbors(x, bx)
        .iter()
        .filter(|s| s.is_some())
        .flat_map(|xx| {
            neighbors(y, by)
                .iter()
                .filter(|t| t.is_some())
                .flat_map(|yy| {
                    neighbors(z, bz)
                        .iter()
                        .filter(|t| t.is_some())
                        .map(|zz| (xx.unwrap(), yy.unwrap(), zz.unwrap()))
                        .filter(|(xx, yy, zz)| {
                            (*xx != x && *yy == y && *zz == z)
                                || (*xx == x && *yy != y && *zz == z)
                                || (*xx == x && *yy == y && *zz != z)
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
}

/// returns all 26 neighbors in 3D space
pub fn cubic_neighbors26(
    x: usize,
    y: usize,
    z: usize,
    bx: usize,
    by: usize,
    bz: usize,
) -> Vec<(usize, usize, usize)> {
    neighbors(x, bx)
        .iter()
        .filter(|s| s.is_some())
        .flat_map(|xx| {
            neighbors(y, by)
                .iter()
                .filter(|t| t.is_some())
                .flat_map(|yy| {
                    neighbors(z, bz)
                        .iter()
                        .filter(|t| t.is_some())
                        .map(|zz| (xx.unwrap(), yy.unwrap(), zz.unwrap()))
                        .filter(|(xx, yy, zz)| !(*xx == x && *yy == y && *zz == z))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
}

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

pub struct Neighbor8Iterator<'a, T> {
    base: &'a Dim2<T>,
    boundary: &'a Dim2<T>,
    index: u8,
}

pub struct Neighbor8Iterator2<'a, T> {
    base: &'a Dim2<T>,
    boundary0: &'a Dim2<T>,
    boundary1: &'a Dim2<T>,
    index: u8,
}

pub trait NeighborIterator<T> {
    /// Iterate on its 8 neighbors.Their positions are in [(0, 0), `boundary1`).
    fn iter8<'a>(&'a self, boundary: &'a Dim2<T>) -> Neighbor8Iterator<'a, T>;
    /// Iterate on its 8 neighbors. Their positions are in [`boundary0`, `boundary1`).
    fn iter8_from<'a>(
        &'a self,
        boundary0: &'a Dim2<T>,
        boundary1: &'a Dim2<T>,
    ) -> Neighbor8Iterator2<'a, T>;
}

impl NeighborIterator<usize> for Dim2<usize> {
    fn iter8<'a>(&'a self, boundary: &'a Dim2<usize>) -> Neighbor8Iterator<'a, usize> {
        Neighbor8Iterator {
            base: self,
            boundary,
            index: 0,
        }
    }
    fn iter8_from<'a>(
        &'a self,
        boundary0: &'a Dim2<usize>,
        boundary1: &'a Dim2<usize>,
    ) -> Neighbor8Iterator2<'a, usize> {
        Neighbor8Iterator2 {
            base: self,
            boundary0,
            boundary1,
            index: 0,
        }
    }
}

impl<'a> Iterator for Neighbor8Iterator<'a, usize> {
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

impl<'a> Iterator for Neighbor8Iterator2<'a, usize> {
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

impl NeighborIterator<isize> for Dim2<isize> {
    fn iter8<'a>(&'a self, boundary: &'a Dim2<isize>) -> Neighbor8Iterator<'a, isize> {
        Neighbor8Iterator {
            base: self,
            boundary,
            index: 0,
        }
    }
    fn iter8_from<'a>(
        &'a self,
        boundary0: &'a Dim2<isize>,
        boundary1: &'a Dim2<isize>,
    ) -> Neighbor8Iterator2<'a, isize> {
        Neighbor8Iterator2 {
            base: self,
            boundary0,
            boundary1,
            index: 0,
        }
    }
}

impl<'a> Iterator for Neighbor8Iterator<'a, isize> {
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

impl<'a> Iterator for Neighbor8Iterator2<'a, isize> {
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
