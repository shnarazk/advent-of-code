import Parsing

private func rotateCCW<T>(_ m: [[T]]) -> [[T]] {
    var t: [[T]] = Array(repeating: [], count: m[0].count)
    for i in m.indices {
        for j in m[i].indices {
            t[j].append(m[i][j])
        }
    }
    return t
}

public func day06(_ data: String) throws {
    let parser: some Parser<Substring, [Int]> = Many {
        Parse {
            Many { " " }
            Int.parser()
        }.map { $0.1 }
    } terminator: {
        Many { " " }
    }
    let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
    let ops = zip(Array(lines.last!), 0...).filter({ ["+", "*"].contains($0.0) })
    let h = rotateCCW(try lines.dropLast().map({ try parser.parse($0) }))
    let tmp1 = zip(ops.map({ $0.0 == "*" }), h)
    let sum1 = tmp1.map({ mul, l in mul ? l.reduce(1, *) : l.reduce(0, +) }).reduce(0, +)
    let vString: [String] = rotateCCW(lines.dropLast().map({ Array($0) })).map({
        String($0).trimmingCharacters(in: .whitespaces)
    })
    var v: [[Int]] = []
    var tmp: [Int] = []
    for n in vString {
        if n == "" {
            v.append(tmp)
            tmp = []
        } else {
            tmp.append(Int(String(n))!)
        }
    }
    v.append(tmp)
    let tmp2 = zip(ops.map({ $0.0 == "*" }), v)
    let sum2 = tmp2.map({ mul, l in mul ? l.reduce(1, *) : l.reduce(0, +) }).reduce(0, +)
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
