import Utils

private func add(_ a: (Int, Int), _ b: (Int, Int)) -> (Int, Int) {
    (a.0 + b.0, a.1 + b.1)
}

private func sub(_ a: (Int, Int), _ b: (Int, Int)) -> (Int, Int) {
    (a.0 - b.0, a.1 - b.1)
}

private func part1(_ size: (Int, Int), _ antennas: [Character: [(Int, Int)]]) -> Int {
    var antis = Set<[Int]>()
    for (_, ans) in antennas {
        for (i, p1) in ans.enumerated() {
            for (j, p2) in ans.enumerated() {
                if i < j {
                    let d = sub(p2, p1)
                    if let p = within(add(p2, d), in: size) {
                        antis.insert([p.0, p.1])
                    }
                    if let p = within(sub(p1, d), in: size) {
                        antis.insert([p.0, p.1])
                    }
                }
            }
        }
    }
    return antis.count
}

private func part2(_ size: (Int, Int), _ antennas: [Character: [(Int, Int)]]) -> Int {
    var antis = Set<[Int]>()
    for (_, ans) in antennas {
        for (i, p1) in ans.enumerated() {
            for (j, p2) in ans.enumerated() {
                if i < j {
                    let d = sub(p2, p1)
                    var x = (0, 0)
                    while let p = within(add(p2, x), in: size) {
                        antis.insert([p.0, p.1])
                        x = add(x, d)
                    }
                    x = (0, 0)
                    while let p = within(sub(p1, x), in: size) {
                        antis.insert([p.0, p.1])
                        x = add(x, d)
                    }
                }
            }
        }
    }
    return antis.count
}

public func day08(_ data: String) {
    let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0) }
    let size = (lines.count, lines[0].count)
    var antennas: [Character: [(Int, Int)]] = [:]
    for (i, l) in lines.enumerated() {
        for (j, c) in l.enumerated() {
            if c != "." {
                antennas[c] = antennas[c, default: [(Int, Int)]()] + [(i, j)]
            }
        }
    }
    let sum1 = part1(size, antennas)
    let sum2 = part2(size, antennas)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
