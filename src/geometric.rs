//! misc functions about 2D/3D computation

/// returns `[self - 1, self, self + 1]`
pub fn neighbors(here: usize, upto: usize) -> [Option<usize>; 3] {
    [
        here.checked_sub(1),
        Some(here),
        (here + 1 < upto).then(|| here + 1),
    ]
}

/// returns all 4 neighbors
/// ```
/// use adventofcode::geometric;
/// assert_eq!(geometric::neighbors4(0, 0, 2, 2), vec![(0, 1), (1, 0)]);
/// assert_eq!(geometric::neighbors4(1, 1, 3, 3), vec![(0, 1), (1, 0), (1, 2), (2, 1)]);
/// assert_eq!(geometric::neighbors4(1, 1, 2, 3), vec![(0, 1), (1, 0), (1, 2)]);
/// assert_eq!(geometric::neighbors4(1, 0, 3, 3), vec![(0, 0), (1, 1), (2, 0)]);
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
