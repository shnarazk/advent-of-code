import Parsing

private func part1(_ input: [(Int, Int)]) -> Int {
    input.indices.map { i in
        input.indices.dropFirst(i + 1).map { j in
            abs(input[i].0 - input[j].0 + 1) * abs(input[i].1 - input[j].1 + 1)
        }.reduce(0, max)
    }.reduce(0, max)
}

private func part2(_ input: [(Int, Int)]) -> Int {
    0
}

public func day09(_ data: String) throws {
    let line_parser: some Parser<Substring, (Int, Int)> = Parse {
        Int.parser()
        ","
        Int.parser()
        "\n"
    }
    let parser: some Parser<Substring, [(Int, Int)]> = Many {
        line_parser
    }
    let input = try parser.parse(data)
    let sum1 = part1(input)
    let sum2 = part2(input)
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
