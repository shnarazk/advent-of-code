import Parsing

private func part1(_ lines: [Int]) -> Int {
    var pos = 50
    var zeros = 0
    for step in lines {
        pos = (pos + step) % 100
        zeros += pos == 0 ? 1 : 0
    }
    return zeros
}

private func part2(_ lines: [Int]) -> Int {
    var pos = 50
    var zeros = 0
    for step in lines {
        let old = pos
        pos += step
        zeros += old > 0 && pos <= 0 ? 1 : 0
        zeros += abs(pos) / 100
        pos = ((pos % 100) + 100) % 100
    }
    return zeros
}

public func day01(_ data: String) {
    let line_parser: some Parser<Substring, Int> = Parse(input: Substring.self) {
        OneOf {
            Parse {
                "L"
                Int.parser()
            }.map { -$0 }
            Parse {
                "R"
                Int.parser()
            }
        }
    }
    .map { $0 }

    let parser: some Parser<Substring, [Int]> = Many {
        line_parser
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    do {
        let lines: [Int] = try parser.parse(data)
        let sum1 = part1(lines)
        let sum2 = part2(lines)
        print("Part1: \(sum1)")
        print("Part2: \(sum2)")
    } catch {
        print(error)
    }
}
