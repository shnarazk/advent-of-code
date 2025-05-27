//
//  day09.swift
//  aoc
//
import Foundation

typealias Record = (pos: Int, id: Int, lenght: Int)

func decode(_ line: [Int]) -> [Record] {
    var map = [Record]()
    func step(_ l: Int, _ status: (Int, Int, Bool)) -> (Int, Int, Bool) {
        if status.2 {
            map.append( (status.0, status.1, l) )
            return (state.0 + l, status.1 + 1, !state.2)
        }
        return (state.0 + l, status.1, !state.2)
    }
    var state = (0, 0, true)  // (start, id, file?)
    for l in line {
        state = step(l,state)
    }
   return map
}

public func day09(_ data: String) {
    let input: [Int] = data.trimmingCharacters(in: CharacterSet.whitespacesAndNewlines).map {
        Int($0.asciiValue! - Character("0").asciiValue!) }

    let initplaces = decode(input)
    print(initplaces)

    func part1(_ data: [Record]) {
        // var lines = lines
        print("Part1: \(1)")
    }

    func part2(_ data: [Record]) {
        // var lines = lines
        print("Part2: \(2)")
    }
//    part1(data)
//    part2(data)
}
