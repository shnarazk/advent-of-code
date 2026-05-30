import Parsing

/// Returns 10^n.
private func pow10(_ n: Int) -> Int {
    return n == 0 ? 1 : 10 * pow10(n - 1)
}

/// Returns the number of decimal digits in `n`.
private func digits(_ n: Int) -> Int {
    return n < 10 ? 1 : 1 + digits(n / 10)
}

/// Extracts the `nth` group of `length` digits from `source`, counted from the left (1-indexed).
/// e.g. `pick(source: 112233, length: 2, nth: 1)` → `11`
private func pick(source: Int, length: Int, nth: Int) -> Int {
    (source / pow10(digits(source) - length * nth)) % pow10(length)
}

/// Returns the number formed by concatenating `source` with itself `n` times.
/// e.g. `repeated(source: 123, count: 4)` → `123_123_123_123`
private func repeated(source: Int, count n: Int) -> Int {
    (1...n).reduce(0, { acc, _ in acc * pow10(digits(source)) + source })
}

/// Returns the sum of all integers in `range` whose digits form `repeating` identical groups.
/// e.g. with `repeating: 2`, valid numbers are 1122, 3344, 111333, …
private func sumOfSatisfiers(range: (Int, Int), repeating: Int) -> Int {
    var s = range.0
    var e = range.1
    var sLen = digits(s)
    var eLen = digits(e)
    if sLen % repeating > 0 {
        sLen = (sLen / repeating + 1) * repeating
        s = pow10(sLen - 1)
    }
    if eLen % repeating > 0 {
        eLen = (eLen / repeating) * repeating
        e = pow10(eLen) - 1
    }
    if s > e {
        return 0
    }
    let len = (digits(s)) / repeating
    var total = 0
    let ss = pick(source: s, length: len, nth: 1)
    let ee = pick(source: e, length: len, nth: 1)
    if ss < ee {
        for d in (ss + 1)..<ee {
            total += repeated(source: d, count: repeating)
        }
    }
    if ss == ee {
        if (1...repeating).allSatisfy({
            pick(source: s, length: len, nth: $0) <= ss
                && pick(source: e, length: len, nth: $0) >= ss
        }) {
            total += repeated(source: ss, count: repeating)
        }
    } else {
        if (1...repeating).allSatisfy({ pick(source: s, length: len, nth: $0) <= ss }) {
            total += repeated(source: ss, count: repeating)
        }
        if (1...repeating).allSatisfy({ pick(source: e, length: len, nth: $0) >= ee }) {
            total += repeated(source: ee, count: repeating)
        }
    }
    return total
}

/// Solves part 1: sum of integers in `range` with digits in 2 repeating groups.
private func part1(range: (Int, Int)) -> Int {
    sumOfSatisfiers(range: range, repeating: 2)
}

private func helper1(range: (Int, Int), set: inout Set<Int>) {
    let sLen = digits(range.0)
    let ss = pick(source: range.0, length: 1, nth: 1)
    let ee = range.1 / pow10(sLen - 1)
    if ss <= ee {
        for d in ss...ee {
            let x = repeated(
                source: pick(source: d, length: 1, nth: 1), count: sLen + digits(d) - 1)
            if x >= 10 && range.0 <= x && x <= range.1 {
                set.insert(x)
            }
        }
    }
}

private func helper2(range: (Int, Int), length: Int, set: inout Set<Int>) {
    var e = range.1
    let eLen = digits(e)
    if eLen / length < 2 { return }
    if eLen % length > 0 { e = pow10((eLen / length) * length) - 1 }
    var s = range.0
    var sLen = digits(s)
    if sLen % length > 0 {
        sLen = (sLen / length + 1) * length
        s = pow10(sLen - 1)
    }
    for d in pick(source: s, length: length, nth: 1)...pick(source: e, length: length, nth: 1) {
        let x = repeated(source: d, count: sLen / length)
        if s <= x && x <= e { set.insert(x) }
    }
}

/// Solves part 2.
private func part2(range: (Int, Int)) -> Int {
    var total: Set<Int> = Set()
    helper1(range: range, set: &total)
    for l in 2...8 {
        helper2(range: range, length: l, set: &total)
    }
    return total.reduce(0, +)
}

public func day02(_ data: String) {
    assert(pick(source: 112233, length: 2, nth: 3) == 33)
    assert(pick(source: 112233, length: 3, nth: 2) == 233)
    assert(repeated(source: 123, count: 4) == 123_123_123_123)
    let pair: some Parser<Substring, (Int, Int)> = Parse {
        Int.parser()
        "-"
        Int.parser()
    }
    let parser: some Parser<Substring, [(Int, Int)]> = Many {
        pair
    } separator: {
        ","
    } terminator: {
        "\n"
    }
    do {
        let input = try parser.parse(data)
        let sum1 = input.map { part1(range: $0) }.reduce(0, +)
        let sum2 = input.map { part2(range: $0) }.reduce(0, +)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
        fatalError()
    }
}
