func within(_ me: (Int, Int), in size: (Int, Int)) -> (Int, Int)? {
    if 0 <= me.0 && me.0 < size.0 && 0 <= me.1 && me.1 < size.1 {
        me
    } else {
        nil
    }
}
private func part1(_ size: (Int, Int), _ mirror: [Character: [(Int, Int)]], _ start: (Int, Int))
    -> Int
{
    0
}

private func part2(_ size: (Int, Int), _ mirror: [Character: [(Int, Int)]], _ start: (Int, Int))
    -> Int
{
    0
}

public func day06(_ data: String) {
    let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0) }
    let size = (lines.count, lines[0].count)
    var mirrors: [Character: [(Int, Int)]] = [:]
    var start: (Int, Int) = (0, 0)
    for (i, l) in lines.enumerated() {
        for (j, c) in l.enumerated() {
            if c == "#" {
                mirrors[c] = mirrors[c, default: []] + [(i, j)]
            } else if c == "^" {
                start = (i, j)
            }
        }
    }
    print(mirrors)
    let sum1 = part1(size, mirrors, start)
    let sum2 = part2(size, mirrors, start)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
