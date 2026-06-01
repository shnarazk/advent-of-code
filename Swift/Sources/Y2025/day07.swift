import Parsing
import Utils

private func evaluate(_ branches: [[Int]], _ start: Int) -> (Int, Int) {
    var count = 0
    var line: [Int: Int] = [start: 1]
    for branch in branches {
        var next: [Int: Int] = [:]
        for (x, n) in line {
            if branch.contains(x) {
                count += 1
                next[x - 1, default: 0] += n
                next[x + 1, default: 0] += n
            } else {
                next[x, default: 0] += n
            }
        }
        line = next
    }
    return (count, line.values.reduce(0, +))
}

private func part2(_ branches: [[Int]], _ start: Int) -> Int {
    var line: [Int: Int] = [start: 1]
    for branch in branches {
        var next: [Int: Int] = [:]
        for (x, n) in line {
            if branch.contains(x) {
                next[x - 1, default: 0] += n
                next[x + 1, default: 0] += n
            } else {
                next[x, default: 0] += n
            }
        }
        line = next
    }
    return line.values.reduce(0, +)
}

public func day07(_ data: String) throws {
    let line_parser: some Parser<Substring, [Character]> = Many {
        First<Substring>()
            .filter { $0 == "." || $0 == "^" || $0 == "S" }
    } terminator: {
        "\n"
    }
    let parser: some Parser<Substring, [[Character]]> = Many {
        line_parser
    }

    // let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
    let grid = try parser.parse(data)
    var start: Pos = Pos(y: 0, x: 0)
    var branches: [[Int]] = []
    outer: for i in grid.indices {
        var l: [Int] = []
        for j in grid[i].indices {
            switch grid[i][j] {
            case "S":
                start = Pos(y: i, x: j)
            case "^":
                l.append(j)
            default:
                break
            }
        }
        branches.append(l)
    }
    let (sum1, sum2) = evaluate(branches, start.x)
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
