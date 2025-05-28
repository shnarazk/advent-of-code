import Parsing

private func part1(_ data: String) -> Int {
    let mul: some Parser<Substring, (Int, Int)> = Parse {
        "mul("
        Int.parser()
        ","
        Int.parser()
        ")"
    }
    var sum = 0
    var i = data.startIndex
    while i < data.endIndex {
        var str = data[i...]
        do {
            let (a, b) = try mul.parse(&str)
            sum += a * b
        } catch {}
        i = data.index(after: i)
    }
    return sum
}

private func part2(_ data: String) -> Int {
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
    var sum = 0
    var mode = true
    var i = data.startIndex
    while i < data.endIndex {
        var str = data[i...]
        do {
            let (a, b) = try mul.parse(&str)
            if mode {
                sum += a * b
            }
            i = data.index(after: i)
            continue
        } catch {}
        do {
            mode = try flip.parse(&str)
            i = data.index(after: i)
            continue
        } catch {}
        i = data.index(after: i)
    }
    return sum
}

public func day03(_ data: String) {
    let sum1 = part1(data)
    let sum2 = part2(data)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
