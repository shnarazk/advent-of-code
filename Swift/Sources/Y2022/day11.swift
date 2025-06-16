//
//  day11.swift
//  aoc
//
import Parsing

@DebugDescription
private class Monkey {
    let id: Int
    var items: [Int]
    let operation: (Bool, Int?)
    let test: Int
    let test_then: Int
    let test_else: Int
    var num_inspect: Int
    init(
        id: Int,
        items: [Int],
        operation: (Bool, Int?),
        test: Int,
        test_then: Int,
        test_else: Int,
    ) {
        self.id = id
        self.items = items
        self.operation = operation
        self.test = test
        self.test_then = test_then
        self.test_else = test_else
        self.num_inspect = 0
    }
    func copy() -> Monkey {
        return Monkey(
            id: self.id,
            items: self.items,
            operation: self.operation,
            test: self.test,
            test_then: self.test_then,
            test_else: self.test_else
        )
    }
    var debugDescription: String {
        "\(id)"
    }
    func update(thrown: inout [[Int]]) {
        for i in self.items {
            self.num_inspect += 1
            var j =
                switch self.operation {
                case (false, let k): i + (k ?? 1)
                case (true, let k): i * (k ?? i)
                }
            j /= 3
            thrown[(j % self.test == 0) ? self.test_then : self.test_else].append(j)
        }
        self.items.removeAll()
    }
    func update2(thrown: inout [[Int]], dividedBy d: Int) {
        for i in self.items {
            self.num_inspect += 1
            let j =
                switch self.operation {
                case (false, let k): i + (k ?? 1)
                case (true, let k): i * (k ?? i)
                }
            thrown[(j % self.test == 0) ? self.test_then : self.test_else].append(j % d)
        }
        self.items.removeAll()
    }
}

private func update(monkeys: inout [Monkey], state: inout [[Int]]) {
    for (i, v) in state.enumerated() {
        if !v.isEmpty {
            state[i] = []
            monkeys[i].items.append(contentsOf: v)
        }
    }
}

private func part1(monkeys: [Monkey]) -> Int {
    var monkeys = monkeys.map { $0.copy() }
    var state: [[Int]] = Array(repeating: Array(), count: monkeys.count)
    for _ in 1...20 {
        for monkey in monkeys {
            monkey.update(thrown: &state)
            update(monkeys: &monkeys, state: &state)
        }
    }
    let v: [Int] = monkeys.map(\.num_inspect).sorted().reversed()
    return v[0] * v[1]
}

private func part2(monkeys: [Monkey]) -> Int {
    var monkeys = monkeys.map { $0.copy() }
    let cd: Int = monkeys.reduce(1) { $0 * $1.test }
    var state: [[Int]] = Array(repeating: Array(), count: monkeys.count)
    for _ in 1...10000 {
        for monkey in monkeys {
            monkey.update2(thrown: &state, dividedBy: cd)
            update(monkeys: &monkeys, state: &state)
        }
    }
    let v: [Int] = monkeys.map(\.num_inspect).sorted().reversed()
    return v[0] * v[1]
}

public func day11(_ data: String) {
    let operation_target: some Parser<Substring, Int?> = OneOf {
        Parse { "old" }.map { _ in nil as Int? }
        Int.parser().map { $0 as Int? }
    }
    let monkey: some Parser<Substring, Monkey> = Parse {
        "Monkey "
        Int.parser()
        ":\n  Starting items: "
        Many {
            Int.parser()
        } separator: {
            ", "
        }
        "\n  Operation: new = old "
        OneOf {
            "* ".map { true }
            "+ ".map { false }
        }
        operation_target
        "\n  Test: divisible by "
        Int.parser()
        "\n    If true: throw to monkey "
        Int.parser()
        "\n    If false: throw to monkey "
        Int.parser()
        "\n"
    }.map { id, items, isMul, num1, test, test_then, test_else in
        Monkey(
            id: id,
            items: items,
            operation: (isMul, num1),
            test: test,
            test_then: test_then,
            test_else: test_else,
        )
    }
    let parser: some Parser<Substring, [Monkey]> = Many {
        monkey
    } separator: {
        "\n"
    }
    do {
        let input = try parser.parse(data)
        let sum1 = part1(monkeys: input)
        let sum2 = part2(monkeys: input)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
        fatalError()
    }
}
