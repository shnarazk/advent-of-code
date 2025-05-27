//
//  day09.swift
//  aoc
//
import Foundation

typealias Record = (pos: Int, id: Int, length: Int)

func decode(_ line: [Int]) -> [Record] {
    var map = [Record]()
    func step(_ l: Int, _ status: (Int, Int, Bool)) -> (Int, Int, Bool) {
        if status.2 {
            map.append((status.0, status.1, l))
            return (state.0 + l, status.1 + 1, !state.2)
        }
        return (state.0 + l, status.1, !state.2)
    }
    var state = (0, 0, true)  // (start, id, file?)
    for l in line {
        state = step(l, state)
    }
    return map
}

/// Return the score
func points(_ data: [Record]) -> Int {
    var p: Int = 0
    for r in data {
        let s = r.pos
        for i in 0..<r.length {
            p += (s + i) * r.id
        }
    }
    return p
}

func part1(_ data: [Record]) {
    var mem = data
    var points = 0
    for i in 0...data.last!.pos + data.last!.length {
        if i < mem.first!.pos {
            points += i * mem.last!.id
            if mem.last!.length == 1 {
                mem.removeLast(1)
                if mem.isEmpty {
                    break
                }
            } else {
                mem[mem.count - 1] = (mem.last!.pos, mem.last!.id, mem.last!.length - 1)
            }
        } else {
            points += i * mem.first!.id
            if mem.first!.pos + mem.first!.length - 1 == i {
                mem.removeFirst(1)
            }
        }
    }
    print("Part1: \(points)")
}

func part2(_ data: [Record]) {
    var mem = data
    for r in data[1...].reversed() {
        for i in 0..<mem.count - 1 {
            let gap = mem[i + 1].pos - (mem[i].pos + mem[i].length)
            if r.length <= gap {
                let pos = mem[i].pos + mem[i].length
                if r.pos < pos {
                    continue
                }
                mem = mem.filter { $0.id != r.id }
                mem.insert((pos: pos, id: r.id, length: r.length), at: i + 1)
                break
            }
        }
    }
    let p = points(mem)
    print("Part2: \(p)")
}

public func day09(_ data: String) {
    let input: [Int] = data.trimmingCharacters(
        in: CharacterSet.whitespacesAndNewlines
    ).map {
        Int($0.asciiValue! - Character("0").asciiValue!)
    }

    let initplaces = decode(input)
    part1(initplaces)
    part2(initplaces)
}
