private func part1(_ size: (Int, Int), _ grid: [[Int]]) -> Int {
    return 0
}

private func part2(_ size: (Int, Int), _ grid: [[Int]]) -> Int {
    return 0
}

public func day10(_ data: String) {
    let grid: [[Int]] = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map {
            Array($0).map { Int(($0 as Character).asciiValue! - Character("0").asciiValue!) }
        }
    let size = (grid.count, grid[0].count)
    print(grid)
    let sum1 = part1(size, grid)
    let sum2 = part2(size, grid)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
