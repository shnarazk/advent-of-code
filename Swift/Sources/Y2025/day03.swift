import Parsing

private func part1(_ input: [[Int]]) -> Int {
    input.map { line in
        var a = Array(line.suffix(2))
        for n in line.reversed().dropFirst(2) {
            if n >= a[0] {
                a[1] = max(a[0], a[1])
                a[0] = n
            }
        }
        return a[0] * 10 + a[1]
    }
    .reduce(0, +)
}

private func part2(_ input: [[Int]]) -> Int {
    input.map { line in
        var a = Array(line.suffix(12))
        for n in line.reversed().dropFirst(12) {
            var x: Int = n
            for i in a.indices {
                if x >= a[i] {
                    (a[i], x) = (x, a[i])
                } else {
                    break
                }
            }
        }
        return a.reduce(0, { acc, n in acc * 10 + n })
    }
    .reduce(0, +)
}

public func day03(_ data: String) {
    let line_parser: some Parser<Substring, [Int]> = Many {
        First<Substring>()
            .filter { $0.isNumber }
            .map { $0.wholeNumberValue! }
    } terminator: {
        "\n"
    }
    let parser: some Parser<Substring, [[Int]]> = Many {
        line_parser
    }
    do {
        let input = try parser.parse(data)
        let sum1 = part1(input)
        let sum2 = part2(input)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
        fatalError()
    }
}
