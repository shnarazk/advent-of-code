import Parsing

func total_order(_ range: [Int], by rules: [(Int, Int)]) -> [Int] {
    let unrestricted: [Int] = range.filter { node in rules.allSatisfy { rule in node != rule.0 } }
    if unrestricted.isEmpty {
        return range
    } else {
        let rs = rules.filter { !unrestricted.contains($0.1) }
        return total_order(range.filter { !unrestricted.contains($0) }, by: rs) + unrestricted
    }
}
func ordered(_ pages: [Int], by rules: [(Int, Int)]) -> [Int] {
    let rs = rules.filter { pages.contains($0.0) && pages.contains($0.1) }
    return total_order(pages, by: rs)
}

func part1(_ pages: [Int], by rules: [(Int, Int)]) -> Int {
    if ordered(pages, by: rules) == pages {
        return pages[pages.count / 2]
    } else {
        return 0
    }
}

func part2(_ pages: [Int], by rules: [(Int, Int)]) -> Int {
    let os = ordered(pages, by: rules)
    if os != pages {
        return os[os.count / 2]
    } else {
        return 0
    }
}

public func day05(_ data: String) {
    let rule_parser = Parse(input: Substring.self) {
        Int.parser()
        "|"
        Int.parser()
    }
    // .map { ($0, $1) }
    let rules_parser = Many {
        rule_parser
    } separator: {
        "\n"
    }

    let update_parser: some Parser<Substring, [Int]> = Many {
        Int.parser()
    } separator: {
        ","
    }
    let updates_parser: some Parser<Substring, [[Int]]> = Many {
        update_parser
    } separator: {
        "\n"
    }
    let parser = Parse(input: Substring.self) {
        rules_parser
        "\n\n"
        updates_parser
    }
    // .map { (a: [(Int, Int)], b: [Int]) in (a, b) }
    do {
        let input = try parser.parse(data[...])
        let rules: [(Int, Int)] = input.0
        let updates: [[Int]] = input.1.filter { !$0.isEmpty }
        let sum1 = (updates.map { part1($0, by: rules) }).reduce(0, +)
        let sum2 = (updates.map { part2($0, by: rules) }).reduce(0, +)
        print("Part1: \(sum1)")
        print("Part2: \(sum2)")
    } catch {
        print("\(error)")
    }
}
