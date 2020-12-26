use {
    // lazy_static::lazy_static,
    // regex::Regex,
    std::io::{self, Read},
};

pub fn day03() {
    let mut buffer = String::new();
    io::stdin().read_to_string(&mut buffer).expect("something wrong");
    let geo: Vec<Vec<char>> = buffer
        .lines()
        .map(|l| l.chars().collect::<Vec<char>>())
        .collect::<Vec<_>>();
    println!("{}", count_for_slope(&geo, 1, 1));
    println!("{}", count_for_slope(&geo, 1, 3));
    println!("{}", count_for_slope(&geo, 1, 5));
    println!("{}", count_for_slope(&geo, 1, 7));
    println!("{}", count_for_slope(&geo, 2, 1));
    println!("{}",
             count_for_slope(&geo, 1, 1)
             * count_for_slope(&geo, 1, 3)
             * count_for_slope(&geo, 1, 5)
             * count_for_slope(&geo, 1, 7)
             * count_for_slope(&geo, 2, 1)
             )
}

fn count_for_slope(geo: &[Vec<char>], row: usize, col: usize) -> usize {
    let mut r = row;
    let mut c = col;
    let mut occ = 0;
    while r < geo.len() {
        occ += access(&geo, r, c);
        r += row;
        c += col;
    }
    occ
}

fn access(geo: &[Vec<char>], row: usize, col: usize) -> usize {
    let line = &geo[row];
    let c = col % line.len();
    (line[c] == '#') as usize
}
