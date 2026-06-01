import Parsing

private func part1(_ ranges: [(Int, Int)], _ availables: [Int]) -> Int {
    availables.filter { id in
        ranges.contains(where: { (b, e) in (b...e) ~= id })
    }
    .count
}

private func part2(_ ranges: [(Int, Int)], _ _: [Int]) -> Int {
    var tick: [Int: (Int, Int)] = [:]
    for (b, e) in ranges {
        tick[b, default: (0, 0)].0 += 1
        tick[e, default: (0, 0)].1 += 1
    }
    var v: [(Int, (Int, Int))] = Array(tick)
    v.sort { $0.0 < $1.0 }
    var count = 0
    var nest = 0
    var start = 0
    for (id, (b, e)) in v {
        if 0 < b {
            if nest == 0 {
                start = id
            }
            nest += b
        }
        if 0 < e {
            nest -= e
            if nest == 0 {
                count += id + 1 - start
            }
        }
    }
    return count
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
