import Parsing

func part1(_ left: [Int], _ right: [Int]) -> Int {
    let l = left.sorted()
    let r = right.sorted()
    return zip(l, r).reduce(0) { $0 + abs($1.0 - $1.1) }
}

func part2(_ left: [Int], _ right: [Int]) -> Int {
    let keys = right.reduce(into: [Int: Int]()) {
        $0[$1] = $0[$1, default: 0] + 1
    }
    return left.reduce(0) { $0 + keys[$1, default: 0] * $1 }
}

public func day01(_ data: String) {
    let line_parser: some Parser<Substring, (Int, Int)> = Parse(input: Substring.self) {
        Int.parser()
        Prefix { !$0.isNumber }
        Int.parser()
    }
    .map { ($0, $2) }

    let parser: some Parser<Substring, [(Int, Int)]> = Many {
        line_parser
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    do {
        let lines: [(Int, Int)] = try parser.parse(data)
        let (left, right) = lines.reduce(([Int](), [Int]())) { (acc, line) in
            (
                acc.0 + [line.0],
                acc.1 + [line.1]
            )
        }
        let sum1 = part1(left, right)
        let sum2 = part2(left, right)
        print("Part1: \(sum1)")
        print("Part2: \(sum2)")
    } catch {
        print(error)
    }
}
