import Parsing

private func part1() -> Int {
    0
}

private func part2() -> Int {
    0
}

public func day(_ data: String) {
    let parser: some Parser<Substring, [Int]> = Many {
        Int.parser()
    } separator: {
        " "
    } terminator: {
        "\n"
    }
    do {
//        let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        let input = try parser.parse(data)
        let sum1 = part1()
        let sum2 = part2()
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
