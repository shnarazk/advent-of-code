import Parsing

private func part1() -> Int {
    0
}

private func part2() -> Int {
    0
}

public func day11(_ data: String) throws {
    let parser: some Parser<Substring, [Int]> = Many {
        Int.parser()
    } separator: {
        " "
    } terminator: {
        "\n"
    }
    // let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
    let input = try parser.parse(data)
    print(input)
    let sum1 = part1()
    let sum2 = part2()
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
