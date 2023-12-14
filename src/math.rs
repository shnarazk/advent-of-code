pub fn gcd(x: usize, y: usize) -> usize {
    if y == 0 {
        x
    } else {
        gcd(y, x % y)
    }
}

pub fn lcm(x: usize, y: usize) -> usize {
    x / gcd(x, y) * y
}

pub fn permutations(from: usize, to: usize) -> Vec<Vec<usize>> {
    fn perm(cands: &[usize]) -> Vec<Vec<usize>> {
        if cands.is_empty() {
            return vec![vec![]];
        }
        let mut ret = Vec::new();
        for c in cands.iter() {
            let remains = cands
                .iter()
                .filter(|i| *i != c)
                .copied()
                .collect::<Vec<usize>>();
            for mut v in perm(&remains).into_iter() {
                v.push(*c);
                ret.push(v);
            }
        }
        ret
    }
    let cands = (from..=to).collect::<Vec<usize>>();
    perm(&cands)
}

pub fn transpose<I: Clone>(v: &Vec<Vec<I>>) -> Vec<Vec<I>> {
    let h = v.len();
    let w = v[0].len();
    (0..w)
        .map(|x| (0..h).map(|y| v[y][x].clone()).collect::<Vec<_>>())
        .collect::<Vec<_>>()
}
