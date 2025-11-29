import Parsing

private func part1() -> Int {
    return 0
}

private func part2() -> Int {
    return 0
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
        let lines: [(Int, Int)] = try parser.parse(data + "\n")
        let (_, _) = lines.reduce(([Int](), [Int]())) { (acc, line) in
            (
                acc.0 + [line.0],
                acc.1 + [line.1]
            )
        }
        let sum1 = part1()
        let sum2 = part2()
        print("Part1: \(sum1)")
        print("Part2: \(sum2)")
    } catch {
        print(error)
    }
}
