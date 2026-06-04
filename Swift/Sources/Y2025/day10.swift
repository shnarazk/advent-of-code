import Parsing

private func part1(_ input: ([Bool], [[Int]], [Int])) -> Int {
    let (goal, _buttons, _) = input
    var checked: Set<[Bool]> = Set()
    var toVisit: Set<[Bool]> = Set()
    var next: Set<[Bool]> = Set()
    toVisit.insert(Array(repeating: false, count: goal.count))
    for i in 1... {
        next.removeAll()
        for s in toVisit {
            if checked.contains(s) {
                continue
            }
            checked.insert(s)
            for button in _buttons {
                var s1 = s
                for bi in button {
                    s1[bi] = !s1[bi]
                }
                if s1 == goal {
                    return i
                }
                if !checked.contains(s1) {
                    next.insert(s1)
                }
            }
        }
        (next, toVisit) = (toVisit, next)
    }
    return goal.count
}

private func part2() -> Int {
    0
}

public func day10(_ data: String) throws {
    let indicators: some Parser<Substring, [Bool]> = Parse {
        "["
        Many {
            First<Substring>()
                .filter { $0 == "#" || $0 == "." }
                .map { $0 == "#" }
        }
        "]"
    }
    let effect: some Parser<Substring, [Int]> = Parse {
        "("
        Many {
            Int.parser()
        } separator: {
            ","
        }
        ")"
    }
    let goal: some Parser<Substring, [Int]> = Parse {
        "{"
        Many {
            Int.parser()
        } separator: {
            ","
        }
        "}"
    }
    let line: some Parser<Substring, ([Bool], [[Int]], [Int])> = Parse {
        indicators
        " "
        Many {
            effect
        } separator: {
            " "
        }
        " "
        goal
    }
    let parser: some Parser<Substring, [([Bool], [[Int]], [Int])]> = Many {
        line
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    let input = try parser.parse(data)
    let sum1 = input.map(part1).reduce(0, +)
    let sum2 = part2()
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
