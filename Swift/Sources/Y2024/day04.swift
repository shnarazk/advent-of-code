//
// day04.swift
// aoc

private func part1(_ lines: [[Character]]) -> Int {
    var count = 0
    for l in lines {
        for i in 0...l.count - 4 {
            if l[i...i + 3] == ["X", "M", "A", "S"] || l[i...i + 3] == ["S", "A", "M", "X"] {
                count += 1
            }
        }
    }
    for i in 0...lines.count - 4 {
        for j in 0...lines[0].count - 1 {
            let picked = [lines[i][j], lines[i + 1][j], lines[i + 2][j], lines[i + 3][j]]
            if picked == ["X", "M", "A", "S"] || picked == ["S", "A", "M", "X"] {
                count += 1
            }
        }
    }
    for i in 0...lines.count - 4 {
        for j in 0...lines[0].count - 4 {
            let picked = [
                lines[i][j], lines[i + 1][j + 1], lines[i + 2][j + 2], lines[i + 3][j + 3],
            ]
            if picked == ["X", "M", "A", "S"] || picked == ["S", "A", "M", "X"] {
                count += 1
            }
        }
    }
    for i in 0...lines.count - 4 {
        for j in 3...lines[0].count - 1 {
            let picked = [
                lines[i][j], lines[i + 1][j - 1], lines[i + 2][j - 2], lines[i + 3][j - 3],
            ]
            if picked == ["X", "M", "A", "S"] || picked == ["S", "A", "M", "X"] {
                count += 1
            }
        }
    }
    return count
}

private func part2(_ lines: [[Character]]) -> Int {
    var count = 0
    for i in 1...lines.count - 2 {
        for j in 1...lines[0].count - 2 {
            if lines[i][j] != "A" {
                continue
            }
            let picked1 = [lines[i - 1][j - 1], lines[i + 1][j + 1]].sorted()
            let picked2 = [lines[i - 1][j + 1], lines[i + 1][j - 1]].sorted()
            if picked1 == ["M", "S"] && picked2 == ["M", "S"] {
                count += 1
            }
        }
    }
    return count
}

public func day04(_ data: String) {
    let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0) }
    let sum1 = part1(lines)
    let sum2 = part2(lines)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
