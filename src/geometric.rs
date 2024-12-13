//! misc functions about 2D/3D computation
use serde::Serialize;

pub trait GeometricMath {
    type BaseType;
    type Vector;
    fn add(&self, other: &Self) -> Self;
    fn sub(&self, other: &Self) -> Self;
    fn add_scalar(&self, other: Self::BaseType) -> Self;
    fn mul_scalar(&self, other: Self::BaseType) -> Self;
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
    fn neighbors4(&self, boundary0: &Self, boundary1: &Self) -> Vec<Self>
    where
        Self: Sized;
    fn neighbors8(&self, boundary0: &Self, boundary1: &Self) -> Vec<Self>
    where
        Self: Sized;
}

pub trait GeometricRotation {
    fn turn_right(&self) -> Self;
    fn turn_left(&self) -> Self;
}

pub type Dim2<L> = (L, L);
pub type Vec2 = (isize, isize);

pub trait AsReference<V> {
    fn as_vec_ref(&self) -> &V;
}

impl<L> AsReference<Dim2<L>> for Dim2<L> {
    #[inline]
    fn as_vec_ref(&self) -> &Dim2<L> {
        self
    }
}

impl<L> AsReference<Dim2<L>> for &Dim2<L> {
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

const DIR4: [Vec2; 4] = [(-1, 0), (0, 1), (1, 0), (0, -1)];

const DIR8: [Vec2; 8] = [
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
    fn add(&self, other: &Self) -> Self {
        (self.0 + other.0, self.1 + other.1)
    }
    fn sub(&self, other: &Self) -> Self {
        (self.0 - other.0, self.1 - other.1)
    }
    fn add_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 + other, self.1 + other)
    }
    fn mul_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 * other, self.1 * other)
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
    fn neighbors4(&self, boundary0: &Self, boundary1: &Self) -> Vec<Self> {
        [self.0 - 1, self.0, self.0 + 1]
            .iter()
            .filter(|s| boundary0.0 <= **s && **s < boundary1.0)
            .flat_map(|y| {
                [self.1 - 1, self.1, self.1 + 1]
                    .iter()
                    .filter(|t| boundary0.1 <= **t && **t < boundary1.1)
                    .filter(|x| *y == self.0 || **x == self.1)
                    .filter(|x| *y != self.0 || **x != self.1)
                    .map(|x| (*y, *x))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    }
    fn neighbors8(&self, boundary0: &Self, boundary1: &Self) -> Vec<Self> {
        [self.0 - 1, self.0, self.0 + 1]
            .iter()
            .filter(|s| boundary0.0 <= **s && **s < boundary1.0)
            .flat_map(|y| {
                [self.1 - 1, self.1, self.1 + 1]
                    .iter()
                    .filter(|t| boundary0.1 <= **t && **t < boundary1.1)
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
    fn add(&self, other: &Self) -> Self {
        (self.0 + other.0, self.1 + other.1)
    }
    fn sub(&self, other: &Self) -> Self {
        (
            self.0.saturating_sub(other.0),
            self.1.saturating_sub(other.1),
        )
    }
    fn add_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 + other, self.1 + other)
    }
    fn mul_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 * other, self.1 * other)
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
    fn neighbors4(&self, boundary0: &Self, boundary1: &Self) -> Vec<Self> {
        (0.max(self.0 as isize - 1) as usize..=self.0 + 1)
            .filter(|s| boundary0.0 <= *s && *s < boundary1.0)
            .flat_map(|y| {
                (0.max(self.1 as isize - 1) as usize..=self.1 + 1)
                    .filter(|t| boundary0.1 <= *t && *t < boundary1.1)
                    .filter(|x| y == self.0 || *x == self.1)
                    .filter(|x| y != self.0 || *x != self.1)
                    .map(|x| (y, x))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    }
    fn neighbors8(&self, boundary0: &Self, boundary1: &Self) -> Vec<Self> {
        [self.0 - 1, self.0, self.0 + 1]
            .iter()
            .filter(|s| boundary0.0 <= **s && **s < boundary1.0)
            .flat_map(|y| {
                [self.1 - 1, self.1, self.1 + 1]
                    .iter()
                    .filter(|t| boundary0.1 <= **t && **t < boundary1.1)
                    .filter(|x| *y != self.0 || **x != self.1)
                    .map(|x| (*y, *x))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    }
}

pub type Dim3<L> = (L, L, L);
pub type Vec3 = (isize, isize, isize);

impl<L> AsReference<Dim3<L>> for Dim3<L> {
    #[inline]
    fn as_vec_ref(&self) -> &Dim3<L> {
        self
    }
}

impl<L> AsReference<Dim3<L>> for &Dim3<L> {
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
    fn add(&self, other: &Self) -> Self {
        (self.0 + other.0, self.1 + other.1, self.2 + other.2)
    }
    fn sub(&self, other: &Self) -> Self {
        (self.0 - other.0, self.1 - other.1, self.2 - other.2)
    }
    fn add_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 + other, self.1 + other, self.2 + other)
    }
    fn mul_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 * other, self.1 * other, self.2 * other)
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
    fn neighbors4(&self, _boundary0: &Self, _boundary1: &Self) -> Vec<Self> {
        unimplemented!()
    }
    fn neighbors8(&self, _boundary0: &Self, _boundary1: &Self) -> Vec<Self> {
        unimplemented!()
    }
}

impl GeometricMath for Dim3<usize> {
    type BaseType = usize;
    type Vector = Vec3;
    fn add(&self, other: &Self) -> Self {
        (self.0 + other.0, self.1 + other.1, self.2 + other.2)
    }
    fn sub(&self, other: &Self) -> Self {
        (
            self.0.saturating_sub(other.0),
            self.1.saturating_sub(other.1),
            self.2.saturating_sub(other.2),
        )
    }
    fn add_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 + other, self.1 + other, self.2 + other)
    }
    fn mul_scalar(&self, other: Self::BaseType) -> Self {
        (self.0 * other, self.1 * other, self.2 * other)
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
    fn neighbors4(&self, _boundary0: &Self, _boundary1: &Self) -> Vec<Self> {
        unimplemented!()
    }
    fn neighbors8(&self, _boundary0: &Self, _boundary1: &Self) -> Vec<Self> {
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

/// returns all 8 neighbors
/// ```
/// use adventofcode::geometric;
/// assert_eq!(geometric::neighbors8(0, 0, 2, 2), vec![(0, 1), (1, 0), (1, 1)]);
/// assert_eq!(geometric::neighbors8(1, 1, 3, 3).len(), 8);
/// assert_eq!(geometric::neighbors8(1, 1, 2, 3), vec![(0, 0), (0, 1), (0, 2), (1, 0), (1, 2)]);
/// assert_eq!(geometric::neighbors8(1, 0, 3, 3), vec![(0, 0), (0, 1), (1, 1), (2, 0), (2, 1)]);
/// ```
pub fn neighbors8(j: usize, i: usize, height: usize, width: usize) -> Vec<(usize, usize)> {
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
        .filter(|(jj, ii)| !(*jj == j && *ii == i))
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
