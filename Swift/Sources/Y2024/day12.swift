//
//  day12.swift
//  aoc
//
import Utils

private class Solver {
    let boundary: Pos
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

    /// Converted from Rust
    func evalate1(at pos: Pos) -> Int {
        if accum[pos] != nil {
            return 0
        }
        guard let c = mapping[pos] else {
            return 0
        }
        var count = 0
        var r: [Pos: Bool?] = [:]
        var to_visit: Set<Pos> = Set([pos])
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

    func evalate2(at pos: Pos) -> Int {
        if accum[pos] != nil {
            return 0
        }
        guard let c = mapping[pos] else {
            return 0
        }
        var count = 0
        var r: [Pos: Bool?] = [:]
        var to_visit: Set<Pos> = Set([pos])
        var h_segs: [Pos: Bool] = [:]
        var v_segs: [Pos: Bool] = [:]
        while let p = to_visit.popFirst() {
            if r[p] == nil {
                if mapping[p] == c {
                    count += 1
                    accum[p] = true
                    r[p] = true
                    
                    if mapping[p + Pos.north] != c {
                        h_segs[p] = false
                    }
                    if mapping[p + Pos.south] != c {
                        h_segs[p + Pos.south] = true
                    }
                    if mapping[p + Pos.west] != c {
                        v_segs[p] = false
                    }
                    if mapping[p + Pos.east] != c {
                        v_segs[p + Pos.east] = true
                    }
                    for q in p.neighbors4(bound: boundary) {
                        to_visit.insert(q)
                    }
                }
            } else {
                r[p] = false
            }
        }
        // build longer segment
        let hss: [Int: [(Int, Bool)]] = h_segs.reduce(into: [:]) { m, pos_spin in
            let pos = pos_spin.0
            let spin = pos_spin.1
            m[pos.y, default: [(Int, Bool)]()].append((pos.x, spin))
        }
        let vss: [Int: [(Int, Bool)]] = v_segs.reduce(into: [:]) { m, pos_spin in
            let pos = pos_spin.0
            let spin = pos_spin.1
            m[pos.x, default: [(Int, Bool)]()].append((pos.y, spin))
        }
        func count_sides(_ dict: [Int: [(Int, Bool)]]) -> Int {
            dict.values.reduce(0) { accum, segs in
                let v = segs.sorted(by: { a, b in a.0 == b.0 ? (a.1 ? 1 : 0) < (b.1 ? 1 : 0): a.0 < b.0 })
                var num = 1
                var end = v[0].0 + 1
                var spin = v[0].1
                for (st, sp) in v[1...] {
                    if end != st || spin != sp {
                        num += 1
                    }
                    end = st + 1
                    spin = sp
                }
                return accum + num
            }
        }
        return count * (count_sides(hss) + count_sides(vss))
    }
}

private func part1(_ solver: Solver) -> Int {
    solver.mapping.keys.reduce(0) {
        $0 + solver.evalate1(at: $1)
    }
}

private func part2(_ solver: Solver) -> Int {
    solver.mapping.keys.reduce(0) {
        $0 + solver.evalate2(at: $1)
    }
}

public func day12(_ data: String) {
    let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0) }
    let solver = Solver(ofMap: lines)
    let sum1 = part1(solver)
    // we reuse solver. So...
    solver.accum.removeAll()
    let sum2 = part2(solver)
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")

}
