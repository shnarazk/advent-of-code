pub fn neighbors(here: usize, upto: usize) -> [Option<usize>; 3] {
    [
        Some(here),
        here.checked_sub(1),
        (here + 1 < upto).then(|| here + 1),
    ]
}
