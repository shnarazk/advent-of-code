import Parsing

let mul: some Parser<Substring, (Int, Int)> = Parse {
    "mul("
    Int.parser()
    ","
    Int.parser()
    ")"
}

let flip: some Parser<Substring, Bool> = Parse {
    "do"
    OneOf {
        "()".map { true }
        "n't()".map { false }
    }
}

func part1(_ data: String) -> Int {
    var sum = 0
    for i in 0..<data.count {
        if data[data.index(data.startIndex, offsetBy: i)] != "m" {
            continue
        }
        do {
            var str = data.dropFirst(i)
            let (a, b) = try mul.parse(&str)
            sum += a * b
        } catch {}
    }
    return sum
}

func part2(_ data: String) -> Int {
    var sum = 0
    var mode = true
    for i in 0..<data.count {
        do {
            var str = data.dropFirst(i)
            let (a, b) = try mul.parse(&str)
            if mode {
                sum += a * b
            }
            continue
        } catch {}
        do {
            var str = data.dropFirst(i)
            mode = try flip.parse(&str)
            continue
        } catch {}
    }
    return sum
}

public func day03(_ data: String) {
    let sum1 = part1(data)
    let sum2 = part2(data)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
