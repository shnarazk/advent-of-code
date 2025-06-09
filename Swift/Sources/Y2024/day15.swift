//
//  day15.swift
//  aoc
//
import Parsing
import Utils

private class Solver {
    var mapping: [[Character]]
    var moves: [Pos]
    var pos: Pos
    // var dir: Pos
    // var posHalf: Bool
    init(mapping: [[Character]], moves: [Pos]) {
        self.mapping = mapping
        self.moves = moves
        // self.next_move = next_move
        self.pos = .east  // pos
        done: for (i, l) in mapping.enumerated() {
            for (j, c) in l.enumerated() {
                if c == "@" {
                    pos = Pos(y: i, x: j)
                    self.mapping[pos] = "."
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
        while mapping[p] == "O" {
            p = p + dir
        }
        if mapping[p] == "." {
            mapping[p] = "O"
            mapping[next] = "."
            pos = next
            // print("Moved to \(pos)")
        }
    }
    func evaluate1() -> Int {
        mapping.enumerated().reduce(0) { acc, il in
            il.1.enumerated().reduce(acc) { acc, jc in
                acc + (jc.1 == "O" ? il.0 * 100 + jc.0 : 0)
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
                print(c, terminator: "")
            }
            print()
        }
    }
    func unsupportedE(pos: Pos, kind: Bool) -> Bool {
        if kind {
            switch mapping[pos] {
            case " ": true
            case "#": false
            // case "O": true
            default: false
            }
        } else {

        }
        return false
    }
}

private func part1(mapping: [[Character]], moves: [Pos]) -> Int {
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
    let grid: some Parser<Substring, [[Character]]> = Parse {
        Many {
            Prefix(1...) { ["#", ".", "O", "@"].contains($0) }
                .map { Array(String($0)) }
        } separator: {
            "\n"
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
    let parser: some Parser<Substring, ([[Character]], [Pos])> = Parse {
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
