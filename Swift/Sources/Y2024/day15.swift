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
}

private class Solver {
    var mapping: [[Kind]]
    var moves: [Pos]
    var pos: Pos
    // var dir: Pos
    // var posHalf: Bool
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
        if !half {
            switch mapping[pos] {
            case .empty: true
            case .wall: false
            case .box: self.unsupportedE(pos + .east, half: half)
            case .boxH: true
            default: fatalError()
            }
        } else {
            switch mapping[pos] {
            case .empty: true
            case .wall: false
            case .box: fatalError()
            case .boxH: self.unsupportedE(pos + .east, half: half)
            default: fatalError()
            }
        }
    }
    func unsupportedW(_ pos: Pos, half: Bool) -> Bool {
        if !half {
            switch mapping[pos] {
            case .empty:
                let w = pos + .west
                return mapping[w] != .boxH || self.unsupportedW(w, half: false)
            case .wall: return false
            case .box: return self.unsupportedW(pos + .west, half: true)
            case .boxH:
                let w = pos + .west
                return mapping[w] != .boxH || self.unsupportedW(w, half: false)
            default: fatalError()
            }
        } else {
            switch mapping[pos] {
            case .empty: return true
            case .wall: return false
            case .box: return self.unsupportedE(pos + .east, half: half)
            case .boxH: fatalError()
            default: fatalError()
            }
        }
    }
    func unsupportedS(_ pos: Pos, half: Bool) -> Bool {
        if !half {
            switch mapping[pos] {
            case .empty:
            case .boxH:
                let w = pos + .west
                let s1 = pos + .south + .west
                let s2 = pos + .south
                return mapping[w] != .boxH
                    || (self.unsupportedS(s1, half: true) && self.unsupportedS(s2, half: false))
            case .wall: return false
            case .box:
                let s = pos + .south
                return self.unsupportedW(s, half: false) && self.unsupportedW(s, half: true)
            default: fatalError()
            }
        } else {
            switch mapping[pos] {
            case .empty: return true
            case .wall: return false
            case .box:
                let s = pos + .south
                return self.unsupportedW(s, half: false) && self.unsupportedW(s, half: true)
            case .boxH:
                let s1 = pos + .south
                let s2 = pos + .south + .east
                return self.unsupportedS(s1, half: true) && self.unsupportedS(s2, half: false)
            default: fatalError()
            }
        }
    }
    func unsupportedN(_ pos: Pos, half: Bool) -> Bool {
        if !half {
            switch mapping[pos] {
            case .wall: return false
            case .empty:
            case .boxH:
                let w = pos + .west
                let n1 = pos + .north
                let n2 = pos + .north + .west
                return mapping[w] != .boxH
                    || (self.unsupportedN(n1, half: false) && self.unsupportedN(n2, half: true))
            case .box:
                let n = pos + .north
                return self.unsupportedN(n, half: false) && self.unsupportedN(n, half: true)
            default: fatalError()
            }
        } else {
            switch mapping[pos] {
            case .empty: return true
            case .wall: return false
            case .box:
                let n = pos + .north
                return self.unsupportedN(n, half: false) && self.unsupportedN(n, half: true)
            case .boxH:
                let n1 = pos + .north
                let n2 = pos + .north + .east
                return self.unsupportedN(n1, half: true) && self.unsupportedN(n2, half: false)
            default: fatalError()
            }
        }
    }
    func unsupported(_ pos: Pos, dir: Pos, half: Bool, direction: Pos) -> Bool {
        switch direction {
        case .north: self.unsupportedN(pos, half: half)
        case .east: self.unsupportedE(pos, half: half)
        case .south: self.unsupportedS(pos, half: half)
        case .west: self.unsupportedW(pos, half: half)
        default: fatalError()
        }
    }
    func shiftE(_ pos: Pos, half: Bool) {
        if !half {
            switch mapping[pos] {
            case .box:
                self.shiftE(pos + .east, half: half)
                mapping[pos] = .boxH
            default:
                return
            }
        } else {
            switch mapping[pos] {
            case .boxH:
                self.shiftE(pos + .east, half: half)
                mapping[pos] = .boxH
            default:
                return
            }
        }
    }
    func shiftW(_ pos: Pos, half: Bool) {
        if !half {
            switch mapping[pos] {
            case .empty:
                let w = pos + .west
                if mapping[w] == .boxH {
                    self.shiftW(w, half: false)
                    mapping[w] = .box
                }
            case .box:
                let w = pos + .west
                self.shiftW(w, half: true)
                mapping[pos] = .empty
                mapping[w] = .boxH
            case .boxH:
                let w = pos + .west
                if mapping[w] == .boxH {
                    self.shiftW(w, half: false)
                    mapping[w] = .box
                }
            default:
                return
            }
        } else {
            switch mapping[pos] {
            case .box:
                let w = pos + .west
                self.shiftE(w, half: half)
                mapping[pos] = .empty
                mapping[w] = .boxH
            default:
                return
            }
        }
    }
    func shiftS(_ pos: Pos, half: Bool) {
        if !half {
            switch mapping[pos] {
            case .empty:
            case .boxH:
                let w = pos + .west
                let s1 = pos + .south + .west
                let s2 = pos + .south
                if mapping[w] == .boxH {
                    self.shiftS(s1, half: true)
                    self.shiftS(s2, half: false)
                    mapping[w] = .empty
                    mapping[s1] = .boxH
                }
            case .box:
                let s = pos + .south
                self.shiftS(s, half: false)
                self.shiftS(s, half: true)
                mapping[pos] = .empty
                mapping[s] = .box
            default:
                return
            }
        } else {
            switch mapping[pos] {
            case .boxH:
                let s1 = pos + .south
                let s2 = pos + .south + .east
                self.shiftS(s1, half: true)
                self.shiftS(s2, half: false)
                mapping[pos] = .empty
                mapping[s1] = .boxH
            case .box:
                let s = pos + .south
                self.shiftS(s, half: false)
                self.shiftS(s, half: true)
                mapping[pos] = .empty
                mapping[s] = .boxH
            default:
                return
            }
        }
    }
    func shiftN(_ pos: Pos, half: Bool) {
        if !half {
            switch mapping[pos] {
            case .empty:
            case .boxH:
                let w = pos + .west
                let n1 = pos + .north + .west
                let n2 = pos + .north
                if mapping[w] == .boxH {
                    self.shiftN(n1, half: true)
                    self.shiftN(n2, half: false)
                    mapping[w] = .empty
                    mapping[n1] = .boxH
                }
            case .box:
                let n = pos + .north
                self.shiftN(n, half: false)
                self.shiftN(n, half: true)
                mapping[pos] = .empty
                mapping[n] = .box
            default:
                return
            }
        } else {
            switch mapping[pos] {
            case .boxH:
                let n1 = pos + .north
                let n2 = pos + .north + .east
                self.shiftN(n1, half: true)
                self.shiftN(n2, half: false)
                mapping[pos] = .empty
                mapping[n1] = .boxH
            case .box:
                let n = pos + .north
                self.shiftN(n, half: false)
                self.shiftN(n, half: true)
                mapping[pos] = .empty
                mapping[n] = .box
            default:
                return
            }
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
    solver.dump()
    return solver.evaluate1()
}

private func part2() -> Int {
    0
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
        let sum2 = part2()
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
        fatalError()
    }
}
