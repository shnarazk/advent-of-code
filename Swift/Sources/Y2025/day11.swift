import Parsing

private struct Path: Hashable {
    let from: String
    let to: String
    init(_ f: String, _ t: String) {
        from = f
        to = t
    }
}

private func countPath(
    _ dict: [String: [String]], _ table: inout [Path: Int], from: String, to: String
) -> Int {
    func get(from: String, to: String) -> Int {
        if let value = table[Path(from, to)] {
            return value
        }
        let count = dict[from, default: []].map({ get(from: $0, to: to) }).reduce(0, +)
        table[Path(from, to)] = count
        return count
    }
    return get(from: from, to: to)
}

private func part1(_ dict: [String: [String]], _ table: inout [Path: Int]) -> Int {
    return countPath(dict, &table, from: "you", to: "out")
}

private func part2(_ dict: [String: [String]], _ table: inout [Path: Int]) -> Int {
    return
        (countPath(dict, &table, from: "svr", to: "fft")
        * countPath(dict, &table, from: "fft", to: "dac")
        * countPath(dict, &table, from: "dac", to: "out"))
        + (countPath(dict, &table, from: "svr", to: "dac")
            * countPath(dict, &table, from: "dac", to: "fft")
            * countPath(dict, &table, from: "fft", to: "out"))
}

public func day11(_ data: String) throws {
    let name: some Parser<Substring, String> = Prefix(3) { $0.isLowercase }.map(String.init)
    let line: some Parser<Substring, (String, [String])> = Parse {
        name
        ": "
        Many {
            name
        } separator: {
            " "
        } terminator: {
            "\n"
        }
    }
    let parser: some Parser<Substring, [(String, [String])]> = Many { line }
    let dict: [String: [String]] = Dictionary(try parser.parse(data), uniquingKeysWith: +)
    var table: [Path: Int] = [:]
    for p in dict {
        for dist in p.1 {
            table[Path(p.0, dist)] = 1
        }
    }
    let sum1 = part1(dict, &table)
    let sum2 = part2(dict, &table)
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
