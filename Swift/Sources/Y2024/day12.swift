//
//  day12.swift
//  aoc
//
import Utils

private class Solver {
    let boundary: Pos
    /// converted from Rust
    let mapping: [Pos: Character]
    var accum: [Pos: Bool] = [:]
    init(boundary: Pos, mapping: [Pos: Character], accum: [Pos: Bool]) {
        self.boundary = boundary
        self.mapping = mapping
        self.accum = accum
    }
    init(ofMap m: [[Character]]) {
        self.boundary = Pos(y: m.count - 1, x: m[0].count - 1)
        var mapping: [Pos: Character] = [:]
        for (y, row) in m.enumerated() {
            for (x, c) in row.enumerated() {
                mapping[Pos(y: y, x: x)] = c
            }
        }
        self.mapping = mapping
    }

    func evalate1(at pos: Pos) -> Int {
        if accum[pos] != nil {
            return 0
        }
        guard let c = mapping[pos] else {
            return 0
        }
        var count = 0
        var r: [Pos: Bool?] = [:]
        var to_visit: Set<Pos> = Set()
        var h_segs: Set<Pos> = Set()
        var v_segs: Set<Pos> = Set()
        while let p = to_visit.popFirst() {
            if r[p] == nil {
                if mapping[p] == c {
                    count += 1
                    accum[p] = true
                    r[p] = true

                    if mapping[p + Pos.north] != c {
                        h_segs.insert(p)
                    }
                    if mapping[p + Pos.south] != c {
                        h_segs.insert(p + Pos.south)
                    }
                    if mapping[p + Pos.west] != c {
                        v_segs.insert(p)
                    }
                    if mapping[p + Pos.east] != c {
                        v_segs.insert(p + Pos.east)
                    }
                    for q in p.neighbors4(bound: boundary) {
                        to_visit.insert(q)
                    }
                }

            } else {
                r[p] = false
            }
        }
        return count * (v_segs.count + h_segs.count)
    }

    func evalate2(_ pos: Pos) -> Int {
        // build longer segment
        let hss = 0  // nil
        let vss = 0  // nil
        func count_sides() -> Int {
            0
        }
        return 0  // count * (v_segs.count + h_segs.count)
    }
}

private func part1(_ solver: Solver) -> Int {
    solver.mapping.keys.reduce(0) {
        $0 + solver.evalate1(at: $1)
    }
}

private func part2(_ solver: Solver) -> Int {
    0
}

public func day12(_ data: String) {
    let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0) }
    let solver = Solver(ofMap: lines)
    let sum1 = part1(solver)
    let sum2 = part2(solver)
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")

}
