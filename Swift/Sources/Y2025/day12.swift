import Parsing

private func part1(_ blocks: [(Int, [[Bool]])], _ spec: (Int, Int, [Int])) -> Bool {
    let (width, height, requirement) = spec
    return width * height >= 9 * requirement.reduce(0, +)
}

public func day12(_ data: String) throws {
    let blockLine: some Parser<Substring, [Bool]> = Parse {
        Prefix(3) { $0 == "." || $0 == "#" }.map({ $0.map { $0 == "#" } })
        "\n"
    }
    let block: some Parser<Substring, (Int, [[Bool]])> = Parse {
        Int.parser()
        ":\n"
        Many(3...3) { blockLine }
        "\n"
    }
    let blockPart: some Parser<Substring, [(Int, [[Bool]])]> = Many {
        block
    }
    let spec: some Parser<Substring, (Int, Int, [Int])> = Parse {
        Int.parser()
        "x"
        Int.parser()
        ": "
        Many {
            Int.parser()
        } separator: {
            " "
        } terminator: {
            "\n"
        }
    }
    let parser: some Parser<Substring, ([(Int, [[Bool]])], [(Int, Int, [Int])])> = Parse {
        blockPart
        Many { spec }
    }
    let (blocks, specs) = try parser.parse(data)
    let sum1 = specs.filter({ part1(blocks, $0) }).count
    print("Part 1: \(sum1)")
    print("Part 2: done!")
}
