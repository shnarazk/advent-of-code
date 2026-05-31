import Parsing

private func part1(_ ranges: [(Int, Int)], _ availables: [Int]) -> Int {
    availables.filter { id in
        ranges.contains(where: { (b, e) in b <= id && id <= e })
    }
    .count
}

private func part2(_ _ranges: [(Int, Int)], _ _availables: [Int]) -> Int {
    0
}

public func day05(_ data: String) {
    let range_parser: some Parser<Substring, (Int, Int)> = Parse {
        Int.parser()
        "-"
        Int.parser()
    }
    let parser_part1: some Parser<Substring, [(Int, Int)]> = Many {
        range_parser
    } separator: {
        "\n"
    }
    let parser_part2: some Parser<Substring, [Int]> = Many {
        Parse {
            Int.parser()
            "\n"
        }
    }
    let parser: some Parser<Substring, ([(Int, Int)], [Int])> = Parse {
        parser_part1
        "\n\n"
        parser_part2
    }
    do {
        let (ranges, avalables) = try parser.parse(data)
        let sum1 = part1(ranges, avalables)
        let sum2 = part2(ranges, avalables)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
        fatalError()
    }
}
