import Collections
import Parsing
import Utils

private struct Ordered<T>: Comparable {
    let priority: Int
    let value: T
    static func < (lhs: Ordered<T>, rhs: Ordered<T>) -> Bool {
        lhs.priority < rhs.priority
    }
    static func == (lhs: Ordered<T>, rhs: Ordered<T>) -> Bool {
        lhs.priority == rhs.priority
    }
}

private func part1(_ input: [Pos3]) -> Int {
    let limit = input.count == 20 ? 10 : 1000
    var heap: Heap<Ordered<(Int, Int)>> = Heap()
    for i in input.indices {
        for j in input.indices {
            if j <= i { continue }
            let p = (input[i] - input[j]).abs()
            let dist = p.z * p.z + p.y * p.y + p.x * p.x
            if heap.count >= limit {
                if heap.max!.priority > dist {
                    heap.removeMax()
                    heap.insert(Ordered(priority: dist, value: (i, j)))
                }
            } else {
                heap.insert(Ordered(priority: dist, value: (i, j)))
            }
        }
    }
    assert(heap.count == limit)
    var groupHeap: [Int] = [0]
    var membership: [Int] = Array(repeating: 0, count: input.count)
    var newGroup = 0
    while let d = heap.popMin() {
        let (i, j) = d.value
        var g1 = membership[i]
        while groupHeap[g1] != 0 {
            g1 = groupHeap[g1]
        }
        var g2 = membership[j]
        while groupHeap[g2] != 0 {
            g2 = groupHeap[g2]
        }
        switch (g1 == 0, g2 == 0) {
        case (false, false):
            if g1 != g2 {
                groupHeap[max(g1, g2)] = min(g1, g2)
            }
        case (false, true):
            membership[j] = membership[i]
        case (true, false):
            membership[i] = membership[j]
        case (true, true):
            newGroup += 1
            groupHeap.append(0)
            membership[i] = newGroup
            membership[j] = newGroup
        }
    }
    var groups: [Int: [Int]] = [:]
    for i in membership.indices {
        var g = membership[i]
        while groupHeap[g] != 0 {
            g = groupHeap[g]
        }
        groups[g, default: []].append(i)
    }
    var gv = groups.map { (id, l) in if id == 0 { 1 } else { l.count } }
    gv.sort(by: { $0 > $1 })
    return gv[0] * gv[1] * gv[2]
}

private func part2(_ input: [Pos3]) -> Int {
    let n = input.count
    var occurred: [Int] = Array(repeating: Int.max, count: input.count)
    var dists: [[Ordered<(Int, Int)>]] = []
    for i in input.indices {
        var minDist = Int.max
        var minIndex = 0
        var ret: [Ordered<(Int, Int)>] = []
        for j in input.indices {
            if j <= i { continue }
            let p = (input[i] - input[j]).abs()
            let dist = p.z * p.z + p.y * p.y + p.x * p.x
            if dist < minDist {
                minDist = dist
                minIndex = j
            }
            ret.append(Ordered(priority: dist, value: (i, j)))
        }
        occurred[i] = min(occurred[i], minDist)
        occurred[minIndex] = min(occurred[minIndex], minDist)
        dists.append(ret)
    }
    let thr = occurred.max()!
    var pickedDists = dists.flatMap { l in
        l.filter { $0.priority <= thr }
    }
    pickedDists.sort(by: { $0.priority < $1.priority })
    var groupHeap: [Int] = [0]
    var membership: [Int] = Array(repeating: 0, count: input.count)
    var newGroup = 0
    var numGroups = 0
    for d in pickedDists {
        let (i, j) = d.value
        var g1 = membership[i]
        while groupHeap[g1] != 0 {
            g1 = groupHeap[g1]
        }
        var g2 = membership[j]
        while groupHeap[g2] != 0 {
            g2 = groupHeap[g2]
        }
        switch (g1 == 0, g2 == 0) {
        case (false, false):
            if g1 != g2 {
                groupHeap[max(g1, g2)] = min(g1, g2)
                numGroups -= 1
            }
        case (false, true):
            membership[j] = membership[i]
        case (true, false):
            membership[i] = membership[j]
        case (true, true):
            newGroup += 1
            numGroups += 1
            groupHeap.append(0)
            membership[i] = newGroup
            membership[j] = newGroup
        }
        if numGroups == 1 && membership.filter({ $0 != 0 }).count == n {
            return input[i].z * input[j].z
        }
    }
    fatalError()
}

public func day08(_ data: String) throws {
    let line_parser: some Parser<Substring, Pos3> = Parse {
        Int.parser()
        ","
        Int.parser()
        ","
        Int.parser()
    }.map { Pos3(z: $0, y: $1, x: $2) }
    let parser: some Parser<Substring, [Pos3]> = Many {
        line_parser
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    let input = try parser.parse(data)
    let sum1 = part1(input)
    let sum2 = part2(input)
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
