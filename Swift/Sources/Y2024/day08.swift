private func part1(_ size: (Int, Int), _ mirrors: Set<[Int]>, ) -> Int? {
    return 0
}

private func part2(_ size: (Int, Int), _ mirrors: Set<[Int]>, ) -> Int {
    return 0
}

public func day08(_ data: String) {
    let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0) }
    let size = (lines.count, lines[0].count)
    var mirrors: Set<[Int]> = Set()
    for (i, l) in lines.enumerated() {
        for (j, c) in l.enumerated() {
            if c == "#" {
                mirrors.insert([i, j])
            }
        }
    }
    let sum1 = 0  // part1(size, mirrors, now, passing, looping)!
    let sum2 = 0  // part2(size, mirrors, now, passing, looping)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
