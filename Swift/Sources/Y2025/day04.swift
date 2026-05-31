import Parsing
import Utils

private func part1(_ grid: [[Bool]]) -> Int {
    var found = 0
    let height = grid.count
    let width = grid.first?.count ?? 0
    let boundary = Pos(y: height - 1, x: width - 1)
    for i in grid.indices {
        for j in grid[i].indices {
            if grid[i][j] {
                var count = 0
                for p in Pos(y: i, x: j).neighbors8(bound: boundary) {
                    if grid[p.y][p.x] {
                        count += 1
                    }
                }
                found += count < 4 ? 1 : 0

            }
        }
    }
    return found
}

private func part2(_ grid: [[Bool]]) -> Int {
    let height = grid.count
    let width = grid.first?.count ?? 0
    let boundary = Pos(y: height - 1, x: width - 1)
    let num_rolls =
        grid
        .map { $0.filter { $0 }.count }
        .reduce(0, +)
    var roll_id: [Pos: Int] = [:]
    var propagate: [[Int]] = Array(repeating: [Int](), count: num_rolls)
    var count: [Int] = Array(repeating: 1, count: num_rolls)
    for i in grid.indices {
        for j in grid[i].indices {
            let p = Pos(y: i, x: j)
            if grid[i][j] {
                roll_id[p] = roll_id[p] ?? roll_id.count
                for q in p.neighbors8(bound: boundary) {
                    if grid[q.y][q.x] {
                        roll_id[q] = roll_id[q] ?? roll_id.count
                        propagate[roll_id[p]!].append(roll_id[q]!)
                        count[roll_id[p]!] += 1
                    }
                }
            }
        }
    }
    var removables: Set<Int> = Set()
    for i in count.indices {
        let c = count[i]
        if c < 5 {
            removables.insert(i)
        }
    }
    var next: Set<Int> = Set()
    var numDeads = 0
    while !removables.isEmpty {
        next.removeAll()
        for p in removables {
            if count[p] > 0 {
                count[p] = 0
                numDeads += 1
                for q in propagate[p] {
                    if count[q] > 0 {
                        count[q] -= 1
                        if count[q] < 5 {
                            next.insert(q)
                        }
                    }
                }
            }
        }
        (next, removables) = (removables, next)
    }
    return numDeads
}

public func day04(_ data: String) {
    let line_parser: some Parser<Substring, [Bool]> = Many {
        First<Substring>()
            .filter { $0 == "@" || $0 == "." }
            .map { $0 == "@" }
    } terminator: {
        "\n"
    }
    let parser: some Parser<Substring, [[Bool]]> = Many {
        line_parser
    }
    do {
        let grid = try parser.parse(data)
        let sum1 = part1(grid)
        let sum2 = part2(grid)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
        fatalError()
    }
}
