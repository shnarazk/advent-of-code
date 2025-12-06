pub fn rotate_clockwise<I: Clone>(m: Vec<Vec<I>>) -> Vec<Vec<I>> {
    let h = m.len();
    let w = m[0].len();
    (0..w)
        .map(|i| (0..h).map(|j| m[h - j - 1][i].clone()).collect::<Vec<_>>())
        .collect::<Vec<_>>()
}

pub fn rotate_ccw<I: Clone>(m: Vec<Vec<I>>) -> Vec<Vec<I>> {
    let h = m.len();
    let w = m[0].len();
    (0..w)
        .map(|i| (0..h).map(|j| m[j][w - i - 1].clone()).collect::<Vec<_>>())
        .collect::<Vec<_>>()
}

#[allow(clippy::ptr_arg)]
pub fn transpose<I: Clone>(v: &Vec<Vec<I>>) -> Vec<Vec<I>> {
    let h = v.len();
    let w = v[0].len();
    (0..w)
        .map(|x| (0..h).map(|y| v[y][x].clone()).collect::<Vec<_>>())
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_rotate_clockwise() {
        let input = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
        let expected_output = vec![vec![7, 4, 1], vec![8, 5, 2], vec![9, 6, 3]];

        assert_eq!(rotate_clockwise(input), expected_output);
    }
    #[test]
    fn test_rotate_ccw() {
        let input = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
        let expected_output = vec![vec![3, 6, 9], vec![2, 5, 8], vec![1, 4, 7]];

        assert_eq!(rotate_ccw(input), expected_output);
    }
    #[test]
    fn test_transpose() {
        let input = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
        let expected_output = vec![vec![1, 4, 7], vec![2, 5, 8], vec![3, 6, 9]];

        assert_eq!(transpose(&input), expected_output);
    }
}
