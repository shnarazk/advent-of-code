//
//  day03.swift
//  aoc
//
import Utils

struct Num {
    let start_pos: Pos
    let val: Int
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
                    nums.append(Num(start_pos: pos!, val: n))
                    picked = nil
                    pos = nil
                }
            }
        }
        if let n = picked {
            nums.append(Num(start_pos: pos!, val: n))
        }
    }
    print(grid)
    print(nums)
    print(symbols)
    let sum1 = 0  // part1(size, grid, starts)
    let sum2 = 0  // part2(size, grid, starts)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
