//
//  day15.swift
//  aoc
//
import Parsing
import Utils

private enum Kind {
    case empty
    case wall
    case box
    case robot
    case boxH
    func asChar2() -> (Character, Character, Character?) {
        return switch self {
        case .empty: (".", ".", nil)
        case .wall: ("#", "#", nil)
        case .box: ("[", "]", nil)
        case .robot: ("@", ".", nil)
        case .boxH: (".", "[", "]")
        }
    }
}

private class Solver {
    var mapping: [[Kind]]
    var moves: [Pos]
    var pos: Pos
    var posHalf: Bool = false
    init(mapping: [[Kind]], moves: [Pos]) {
        self.mapping = mapping
        self.moves = moves
        // self.next_move = next_move
        self.pos = .east  // pos
        done: for (i, l) in mapping.enumerated() {
            for (j, c) in l.enumerated() {
                if c == .robot {
                    pos = Pos(y: i, x: j)
                    self.mapping[pos] = .empty
                    break done
                }
            }
        }
        // self.dir = .north
        // self.posHalf = false
    }
    func press(_ ix: Int) {
        let dir = moves[ix]
        let next = pos + dir
        var p = next
        while mapping[p] == .box {
            p = p + dir
        }
        if mapping[p] == .empty {
            mapping[p] = .box
            mapping[next] = .empty
            pos = next
            // print("Moved to \(pos)")
        }
    }
    func evaluate1() -> Int {
        mapping.enumerated().reduce(0) { acc, il in
            il.1.enumerated().reduce(acc) { acc, jc in
                acc + (jc.1 == .box ? il.0 * 100 + jc.0 : 0)
            }
        }
    }
    func dump() {
        for (i, l) in mapping.enumerated() {
            for (j, c) in l.enumerated() {
                let p = Pos(y: i, x: j)
                if p == pos {
                    print("@", terminator: "")
                    continue
                }
                let ch =
                    switch c {
                    case .empty: "."
                    case .wall: "#"
                    case .box: "O"
                    default: " "
                    }
                print(ch, terminator: "")
            }
            print()
        }
    }
    func unsupportedE(_ pos: Pos, half: Bool) -> Bool {
        let e = pos + .east
        if !half {
            return switch mapping[pos] {
            case .empty: true
            case .wall: false
            case .box: self.unsupportedE(e, half: half)
            case .boxH: true
            default: fatalError()
            }
        } else {
            return switch mapping[pos] {
            case .empty: true
            case .wall: false
            case .box: fatalError()
            case .boxH: self.unsupportedE(e, half: half)
            default: fatalError()
            }
        }
    }
    func unsupportedW(_ pos: Pos, half: Bool) -> Bool {
        let w = pos + .west
        if !half {
            return switch mapping[pos] {
            case .empty: mapping[w] != .boxH || self.unsupportedW(w, half: false)
            case .wall: false
            case .box: self.unsupportedW(w, half: true)
            case .boxH: mapping[w] != .boxH || self.unsupportedW(w, half: false)
            default: fatalError()
            }
        } else {
            return switch mapping[pos] {
            case .empty: true
            case .wall: false
            case .box: self.unsupportedW(w, half: half)
            case .boxH: fatalError()
            default: fatalError()
            }
        }
    }
    func unsupportedS(_ pos: Pos, half: Bool) -> Bool {
        let s = pos + .south
        if !half {
            switch mapping[pos] {
            case .wall: return false
            case .empty, .boxH:
                let w = pos + .west
                let sw = pos + .south + .west
                return mapping[w] != .boxH
                    || (self.unsupportedS(sw, half: true) && self.unsupportedS(s, half: false))
            case .box: return self.unsupportedS(s, half: false) && self.unsupportedS(s, half: true)
            default: fatalError()
            }
        } else {
            switch mapping[pos] {
            case .empty: return true
            case .wall: return false
            case .box: return self.unsupportedS(s, half: false) && self.unsupportedS(s, half: true)
            case .boxH:
                let se = pos + .south + .east
                return self.unsupportedS(s, half: true) && self.unsupportedS(se, half: false)
            default: fatalError()
            }
        }
    }
    func unsupportedN(_ pos: Pos, half: Bool) -> Bool {
        let n = pos + .north
        if !half {
            switch mapping[pos] {
            case .wall: return false
            case .empty, .boxH:
                let w = pos + .west
                let nw = pos + .north + .west
                return mapping[w] != .boxH
                    || (self.unsupportedN(nw, half: true) && self.unsupportedN(n, half: false))
            case .box: return self.unsupportedN(n, half: false) && self.unsupportedN(n, half: true)
            default: fatalError()
            }
        } else {
            switch mapping[pos] {
            case .empty: return true
            case .wall: return false
            case .box: return self.unsupportedN(n, half: false) && self.unsupportedN(n, half: true)
            case .boxH:
                let ne = pos + .north + .east
                return self.unsupportedN(n, half: true) && self.unsupportedN(ne, half: false)
            default: fatalError()
            }
        }
    }
    func unsupported(_ pos: Pos, half: Bool, dir: Pos) -> Bool {
        switch dir {
        case .north: self.unsupportedN(pos, half: half)
        case .east: self.unsupportedE(pos, half: half)
        case .south: self.unsupportedS(pos, half: half)
        case .west: self.unsupportedW(pos, half: half)
        default: fatalError()
        }
    }
    func shiftE(_ pos: Pos, half: Bool) {
        let e = pos + .east
        if !half {
            switch mapping[pos] {
            case .empty: return
            case .box:
                self.shiftE(e, half: half)
                mapping[pos] = .boxH
            case .boxH: return
            default: fatalError()
            }
        } else {
            switch mapping[pos] {
            case .empty: return
            case .boxH:
                self.shiftE(e, half: half)
                mapping[pos] = .empty
                mapping[e] = .box
            default: fatalError()
            }
        }
    }
    func shiftW(_ pos: Pos, half: Bool) {
        let w = pos + .west
        if !half {
            switch mapping[pos] {
            case .empty:
                if mapping[w] == .boxH {
                    self.shiftW(w, half: false)
                    mapping[w] = .box
                }
            case .box:
                self.shiftW(w, half: true)
                mapping[pos] = .empty
                mapping[w] = .boxH
            case .boxH:
                if mapping[w] == .boxH {
                    self.shiftW(w, half: false)
                    mapping[w] = .box
                }
            default: fatalError()
            }
        } else {
            switch mapping[pos] {
            case .empty: return
            case .box:
                self.shiftW(w, half: half)
                mapping[pos] = .empty
                mapping[w] = .boxH
            default: return
            }
        }
    }
    func shiftS(_ pos: Pos, half: Bool) {
        let s = pos + .south
        if !half {
            switch mapping[pos] {
            case .empty, .boxH:
                let w = pos + .west
                let sw = pos + .south + .west
                if mapping[w] == .boxH {
                    self.shiftS(sw, half: true)
                    self.shiftS(s, half: false)
                    mapping[w] = .empty
                    mapping[sw] = .boxH
                }
            case .box:
                self.shiftS(s, half: false)
                self.shiftS(s, half: true)
                mapping[pos] = .empty
                mapping[s] = .box
            default: fatalError()
            }
        } else {
            switch mapping[pos] {
            case .empty: return
            case .boxH:
                let se = pos + .south + .east
                self.shiftS(s, half: true)
                self.shiftS(se, half: false)
                mapping[pos] = .empty
                mapping[s] = .boxH
            case .box:
                self.shiftS(s, half: false)
                self.shiftS(s, half: true)
                mapping[pos] = .empty
                mapping[s] = .box
            default: fatalError()
            }
        }
    }
    func shiftN(_ pos: Pos, half: Bool) {
        let n = pos + .north
        if !half {
            switch mapping[pos] {
            case .empty, .boxH:
                let w = pos + .west
                let nw = pos + .north + .west
                if mapping[w] == .boxH {
                    self.shiftN(nw, half: true)
                    self.shiftN(n, half: false)
                    mapping[w] = .empty
                    mapping[nw] = .boxH
                }
            case .box:
                self.shiftN(n, half: false)
                self.shiftN(n, half: true)
                mapping[pos] = .empty
                mapping[n] = .box
            default: fatalError()
            }
        } else {
            switch mapping[pos] {
            case .empty: return
            case .boxH:
                let ne = pos + .north + .east
                self.shiftN(n, half: true)
                self.shiftN(ne, half: false)
                mapping[pos] = .empty
                mapping[n] = .boxH
            case .box:
                self.shiftN(n, half: false)
                self.shiftN(n, half: true)
                mapping[pos] = .empty
                mapping[n] = .box
            default: fatalError()
            }
        }
    }
    func shift(_ pos: Pos, half: Bool, dir: Pos) {
        switch dir {
        case .north: self.shiftN(pos, half: half)
        case .east: self.shiftE(pos, half: half)
        case .south: self.shiftS(pos, half: half)
        case .west: self.shiftW(pos, half: half)
        default: fatalError()
        }
    }
    func press2(_ t: Int) {
        let dir = moves[t]
        let next =
            switch (dir, posHalf) {
            case (.north, let b): (pos + .north, b)
            case (.south, let b): (pos + .south, b)
            case (.east, false): (pos, true)
            case (.east, true): (pos + .east, false)
            case (.west, false): (pos + .west, true)
            case (.west, true): (pos, false)
            default: fatalError()
            }
        if self.unsupported(next.0, half: next.1, dir: dir) {
            self.shift(next.0, half: next.1, dir: dir)
            pos = next.0
            posHalf = next.1
        }
    }
    func evaluate2() -> Int {
        mapping.enumerated().reduce(0) { acc, il in
            il.1.enumerated().reduce(acc) { acc, jc in
                if jc.1 == .box {
                    acc + il.0 * 100 + jc.0 * 2
                } else if jc.1 == .boxH {
                    acc + il.0 * 100 + jc.0 * 2 + 1
                } else {
                    acc
                }
            }
        }
    }
    func dump2() {
        func str(_ ch: Character?) -> String {
            guard let ch = ch else { return "" }
            return String(ch)
        }
        for (i, l) in mapping.enumerated() {
            var s: String = ""
            var follow: Character? = nil
            for (j, c) in l.enumerated() {
                let p = Pos(y: i, x: j)
                if p == pos {
                    if self.posHalf {
                        s.append(str(follow ?? "."))
                        s.append("@")
                        follow = nil
                    } else if c == .boxH {
                        let (_, b, f) = Kind.boxH.asChar2()
                        s.append("@")
                        s.append(str(b))
                        follow = f
                    } else {
                        s.append("@.")
                        follow = nil
                    }
                    continue
                }
                let (a, b, f) = c.asChar2()
                s.append(follow ?? a)
                s.append(b)
                follow = f
            }
            print(s)
        }
    }
}

private func part1(mapping: [[Kind]], moves: [Pos]) -> Int {
    let solver = Solver(mapping: mapping, moves: moves)
    for t in 0..<moves.count {
        // print("Move: \(moves[t])")
        solver.press(t)
        // solver.dump()
    }
    // solver.dump()
    return solver.evaluate1()
}
private func part2(mapping: [[Kind]], moves: [Pos]) -> Int {
    let solver = Solver(mapping: mapping, moves: moves)
    for t in 0..<moves.count {
        // print("Move: \(moves[t])")
        solver.press2(t)
    }
    // solver.dump2()
    return solver.evaluate2()
}

public func day15(_ data: String) {
    let grid: some Parser<Substring, [[Kind]]> = Parse {
        Many {
            Prefix(1...) { ["#", ".", "O", "@"].contains($0) }
        } separator: {
            "\n"
        }
    }.map {
        $0.map {
            $0.map {
                switch $0 {
                case ".": Kind.empty
                case "#": .wall
                case "O": .box
                case "@": .robot
                default: fatalError()
                }
            }

        }
    }
    let moves: some Parser<Substring, [Pos]> = Parse {
        Prefix { ["^", ">", "v", "<", "\n"].contains($0) }
            .map { Array($0.filter { $0 != "\n" }) }
    }.map {
        Array($0).map {
            switch $0 {
            case "^": .north
            case ">": .east
            case "v": .south
            case "<": .west
            default: fatalError()
            }
        }
    }
    let parser: some Parser<Substring, ([[Kind]], [Pos])> = Parse {
        grid
        moves
    }
    do {
        let (mapping, moves) = try parser.parse(data)
        let sum1 = part1(mapping: mapping, moves: moves)
        let sum2 = part2(mapping: mapping, moves: moves)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
        fatalError()
    }
}
