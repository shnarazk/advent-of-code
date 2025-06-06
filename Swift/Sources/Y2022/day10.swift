//
//  day10.swift
//  aoc
//
import Parsing

private enum Instruction {
    case addx(Int)
    case noop
}

@DebugDescription
private class CPU {
    var pc: Int = 0
    var regX: Int = 1
    var clock: Int = 0
    var working: Int = 0
    let instructions: [Instruction]

    init(instructions: [Instruction]) {
        self.instructions = instructions
    }

    var debugDescription: String {
        "regX: \(regX), clock: \(clock), pc: \(pc)"
    }

    func step() -> [(clock: Int, regX: Int)]? {
        guard pc < instructions.count else {
            if 0 != working {
                regX += working
                clock += 1
                working = 0
                return [(clock: clock, regX: regX)]
            } else {
                return nil
            }
        }
        regX += working
        working = 0
        clock += 1
        switch instructions[pc] {
        case .addx(let value):
            let c1 = (clock: clock, regX: regX)
            working = value
            pc += 1
            clock += 1
            let c2 = (clock: clock, regX: regX)
            return [c1, c2]
        case .noop:
            pc += 1
            return [(clock: clock, regX: regX)]
        }
    }
}

private func part1(_ instructions: [Instruction]) -> Int {
    let cpu = CPU(instructions: instructions)
    var signalStrength: Int = 0
    while let l = cpu.step() {
        if l.count == 0 {
            break
        }
        for state in l {
            if [20, 60, 100, 140, 180, 220].contains(state.clock) {
                signalStrength += state.clock * state.regX
            }
        }
    }
    return signalStrength
}

private func part2(_ instructions: [Instruction]) -> Int {
    let cpu = CPU(instructions: instructions)
    while let l = cpu.step() {
        if l.count == 0 {
            break
        }
        for state in l {
            let x = (state.clock - 1) % 40
            print(abs(x - state.regX) <= 1 ? "#" : " ", terminator: "")
            if x == 39 {
                print()
            }
        }
    }
    return 0
}

public func day10(_ data: String) {
    let instruction: some Parser<Substring, Instruction> = OneOf {
        Parse {
            "addx "
            Int.parser()
        }.map { .addx($0) }
        "noop".map { _ in .noop }
    }
    let parser: some Parser<Substring, [Instruction]> = Many {
        instruction
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    do {
        let input = try parser.parse(data)
        let sum1 = part1(input)
        print("Part 1: \(sum1)")
        print("Part 2:")
        let _ = part2(input)
    } catch {
        print(error)
    }
}
