//
//  day05.swift
//  aoc
//
import Parsing

private struct Rule {
    var from: Int
    var len: Int
    var mapTo: Int
    var to: Int {
        from + len - 1
    }
}

@DebugDescription
private struct Segment {
    // closed end
    var from: Int
    // open end
    var len: Int
    var debugDescription: String {
        "(from: \(from),len: \(len))"
    }
    /// closed end
    var to: Int {
        from + len - 1
    }
    init(from: Int, len: Int) {
        assert(0 <= from)
        assert(0 < len)
        self.from = from
        self.len = len
    }
    init(from: Int, to: Int) {
        assert(0 <= from)
        assert(to >= from)
        self.from = from
        self.len = to - from + 1
    }
    /// Partition to affected one and not-affected parts
    func overlap(_ rule: Rule) -> ([Segment], [Segment]) {
        // There are 6 cases
        //        [.self.]
        // [rule]
        if rule.to < self.from {
            return ([], [self])
        }
        //        [.self.]
        //  [..rule..]
        if rule.from <= self.from && self.from <= rule.to && rule.to < self.to {
            assert(self.len == Segment(from: self.from, to: rule.to).len + Segment(from: rule.to + 1, to: self.to).len)
            return (
                [Segment(from: self.from, to: rule.to)],
                [Segment(from: rule.to + 1, to: self.to)]
            )
        }
        //        [.self.]
        //   [....rule.....]
        if rule.from <= self.from && self.to <= rule.to {
            return ([self], [])
        }
        //        [.self.]
        //         [rule]
        if self.from < rule.from && rule.to < self.to {
            assert(
                self.len == Segment(from: rule.from, to: rule.to).len
                + Segment(from: self.from, to: rule.from - 1).len
                + Segment(from: rule.to + 1, to: self.to).len
            )
            return (
                [Segment(from: rule.from, to: rule.to)],
                [
                    Segment(from: self.from, to: rule.from - 1),
                    Segment(from: rule.to + 1, to: self.to),
                ]
            )
        }
        //        [.self.]
        //         [..rule..]
        if self.from < rule.from && rule.from <= self.to && self.to <= rule.to {
            assert(self.len == Segment(from: rule.from, to: self.to).len + Segment(from: self.from, to: rule.from - 1).len)
            return (
                [Segment(from: rule.from, to: self.to)],
                [Segment(from: self.from, to: rule.from - 1)]
            )
        }
        //        [.self.]
        //                 [rule]
        if self.to < rule.from {
            return ([], [self])
        }
        fatalError()
    }
    func shift(_ rule: Rule) -> Segment {
        Segment(from: self.from + (rule.mapTo - rule.from), len: self.len)
    }
}

private func mapTo(_ rules: [Rule], _ p: Int) -> Int {
    for rule in rules {
        if rule.from <= p && p < rule.from + rule.len {
            return p + (rule.mapTo - rule.from)
        }
    }
    return p
}

private func mapSegmentTo(_ rules: [Rule], _ seg: Segment) -> [Segment] {
    var moved: [Segment] = []
    var unprocessed: [Segment] = [seg]
    for rule in rules {
        var tmp: [Segment] = []
        for segment in unprocessed {
            let (ms, us) = segment.overlap(rule)
            moved += ms.map { $0.shift(rule) }
            tmp += us
        }
        unprocessed = tmp
    }
    return moved + unprocessed
}

private func part1(_ stages: [(String, String, [Rule])], _ src: [Int]) -> Int {
    stages.reduce(src) { seq, stage in seq.map { mapTo(stage.2, $0) } }.min()!
}

private func part2(_ stages: [(String, String, [Rule])], _ segs: [Segment]) -> Int {
    stages.reduce(segs) { segs, stage in
        segs.flatMap { mapSegmentTo(stage.2, $0) } }
        .map { $0.from }
        .min()!
}

public func day05(_ data: String) {
    // Many accepts empty int sequence!kk
    let ints: some Parser<Substring, [Int]> = Parse {
        Int.parser()
        " "
        Many {
            Int.parser()
        } separator: {
            " "
        }
    }.map { [$0] + $1 }
    let rule: some Parser<Substring, Rule> = Parse {
        Int.parser()
        " "
        Int.parser()
        " "
        Int.parser()
    }.map { Rule(from: $1, len: $2, mapTo: $0) }
    let seeds_parser: some Parser<Substring, [Int]> = Parse {
        "seeds: "
        ints
    }
    let block_parser: some Parser<Substring, (String, String, [Rule])> = Parse {
        Prefix { $0 != "-" }
        "-to-"
        Prefix { $0 != " " }
        " map:\n"
        Many {
            rule
        } separator: {
            "\n"
        }
    }.map { (String($0), String($1), $2) }
    let parser: some Parser<Substring, ([Int], [(String, String, [Rule])])> = Parse {
        seeds_parser
        "\n\n"
        Many {
            block_parser
        } terminator: {
            "\n"
        }
    }
    do {
        let input = try parser.parse(data)
        let sum1 = part1(input.1, input.0)
        let segments = (0..<(input.0.count / 2)).map {
            Segment(from: input.0[2 * $0], len: input.0[2 * $0 + 1])
        }
        let sum2 = part2(input.1, segments)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
