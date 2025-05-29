import Utils

private func part1(_ size: (Int, Int), _ antennas: [Character: [Pos]]) -> Int {
    let boundary = Pos.asBoundary(size)
    var antis = Set<Pos>()
    for (_, ans) in antennas {
        for (i, p1) in ans.enumerated() {
            for (j, p2) in ans.enumerated() {
                if i < j {
                    let d = p2 - p1
                    if let p = (p2 + d).within(boundary) {
                        antis.insert(p)
                    }
                    if let p = (p1 - d).within(boundary) {
                        antis.insert(p)
                    }
                }
            }
        }
    }
    return antis.count
}

private func part2(_ size: (Int, Int), _ antennas: [Character: [Pos]]) -> Int {
    let boundary = Pos.asBoundary(size)
    var antis = Set<Pos>()
    for (_, ans) in antennas {
        for (i, p1) in ans.enumerated() {
            for (j, p2) in ans.enumerated() {
                if i < j {
                    let d = p2 - p1
                    var x = Pos.zero
                    while let p = (p2 + x).within(boundary) {
                        antis.insert(p)
                        x = x + d
                    }
                    x = Pos.zero
                    while let p = (p1 - x).within(boundary) {
                        antis.insert(p)
                        x = x + d
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
    var antennas: [Character: [Pos]] = [:]
    for (i, l) in lines.enumerated() {
        for (j, c) in l.enumerated() {
            if c != "." {
                antennas[c] = antennas[c, default: [Pos]()] + [Pos(y: i, x: j)]
            }
        }
    }
    let sum1 = part1(size, antennas)
    let sum2 = part2(size, antennas)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
