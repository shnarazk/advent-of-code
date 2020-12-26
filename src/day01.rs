pub fn day01(_part: usize, buffer: String) {
    let mut v: Vec<usize> = Vec::new();
    for s in buffer.lines() {
        v.push(s.parse::<usize>().expect("bad int"));
    }
    for i in &v {
        for j in &v {
            if i + j == 2020 {
                println!("{} * {} = {}", i, j, i * j)
            }
        }
    }
    for (i, x) in v.iter().enumerate() {
        for (j, y) in v.iter().enumerate().skip(i) {
            for z in v.iter().skip(j) {
                if x + y + z == 2020 {
                    println!("{} * {} * {} = {}", x, y, z, x * y * z);
                }
            }
        }
    }
}
