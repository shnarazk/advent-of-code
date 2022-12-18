//! misc functions about 2D/3D computation

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
