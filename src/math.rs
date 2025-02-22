pub fn gcd(x: usize, y: usize) -> usize {
    if y == 0 { x } else { gcd(y, x % y) }
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

/// Chinese Remainder Theorem
/// Return `x` such that:
/// * x `mod` aq = ar
/// * x `mod` bq = br
///
/// ```
/// use crate::adventofcode::math::*;
/// let a = crt((5, 4), (2, 0));
/// assert_eq!(a.1, 14);
/// ```
pub fn crt((aq, ar): (usize, usize), (bq, br): (usize, usize)) -> (usize, usize) {
    if ar == 0 && br == 0 {
        return (lcm(aq, bq), 0);
    }
    let n = solve1(aq, bq);
    let nar = (n * ar) % bq;
    let nbr = (n * br) % bq;
    let m = if nar < nbr {
        nbr - nar
    } else {
        (bq + nbr) - nar
    };
    (aq * bq, aq * m + ar)
}

/// Return `X` such that:
/// (X * a) `mod` m = ((X * b) `mod` m) + 1
///
fn solve1(a: usize, m: usize) -> usize {
    for i in 0.. {
        if (i * a) % m == 1 {
            return i;
        }
    }
    panic!("can't");
}
