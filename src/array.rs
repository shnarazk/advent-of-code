pub fn rotate_clockwise<I: Clone>(m: Vec<Vec<I>>) -> Vec<Vec<I>> {
    let h = m.len();
    let mut n = m.clone();
    for (y, l) in n.iter_mut().enumerate() {
        for (x, p) in l.iter_mut().enumerate() {
            *p = m[h - x - 1][y].clone();
        }
    }
    n
}

pub fn transpose<I: Clone>(v: &Vec<Vec<I>>) -> Vec<Vec<I>> {
    let h = v.len();
    let w = v[0].len();
    (0..w)
        .map(|x| (0..h).map(|y| v[y][x].clone()).collect::<Vec<_>>())
        .collect::<Vec<_>>()
}
