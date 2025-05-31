//
//  day03.swift
//  aoc
//
import Utils

private struct Num {
    let start_pos: Pos
    let end_pos: Pos
    let val: Int
    func adjacent(_ p: Pos) -> Bool {
        start_pos.y - 1 <= p.y && p.y <= end_pos.y + 1 && start_pos.x - 1 <= p.x && p.x <= end_pos.x + 1
    }
}

private func part1(_ nums: [Num], _ symbols: [Pos]) -> Int {
    nums.map { num in !symbols.allSatisfy { sym in !num.adjacent(sym) } ? num.val : 0 }
        .reduce(0, +)
}

private func part2(_ nums: [Num], _ symbols: [Pos]) -> Int {
    symbols.map { sym in
        let ns = nums.filter { $0.adjacent(sym) }
        return ns.count == 2 ? ns.map { $0.val } .reduce(1) { $0 * $1 } : 0
    }
    .reduce(0, +)
}

public func day03(_ data: String) {
    let grid: [[Character]] = Array(
        data.split(separator: "\n", omittingEmptySubsequences: true)
    )
    .map {
        Array($0).map { $0 as Character }  //  /* Int(($0 as Character).asciiValue! - Character("0").asciiValue!) */ }
    }
    var symbols: [Pos] = []
    var nums: [Num] = []

    for (i, l) in grid.enumerated() {
        var pos: Pos? = nil
        var picked: Int? = nil
        for (j, n) in l.enumerated() {
            if n.isNumber {
                if pos == nil {
                    pos = Pos(y: i, x: j)
                }
                picked =
                    (picked ?? 0) * 10
                    + Int(n.asciiValue! - Character("0").asciiValue!)
            } else {
                if n != "." {
                    symbols.append(Pos(y: i, x: j))
                }
                if let n = picked {
                    nums.append(Num(start_pos: pos!, end_pos: Pos(y: pos!.y, x: j-1), val: n))
                    picked = nil
                    pos = nil
                }
            }
        }
        if let n = picked {
            nums.append(Num(start_pos: pos!, end_pos: Pos(y: pos!.y, x: l.count - 1), val: n))
        }
    }
    let sum1 = part1(nums, symbols)
    let sum2 = part2(nums, symbols)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
