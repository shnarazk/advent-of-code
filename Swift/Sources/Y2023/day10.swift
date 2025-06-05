//
//  day10.swift
//  aoc
//
import Parsing
import Utils
import SwiftUI
import Charts
import SwiftData

@DebugDescription
private struct Cursor {
    var pos: Pos
    var dir: Pos
    var steps: Int = 0
    var debugDescription: String {
        "(\(pos), \(dir), \(steps))"
    }
    func goForward(_ grid: [[Character]]) -> Cursor? {
        switch (grid[pos], dir) {
        case ("|", .north): Cursor(pos: pos + .north, dir: dir, steps: steps + 1)
        case ("|", .south): Cursor(pos: pos + .south, dir: dir, steps: steps + 1)
        case ("-", .east): Cursor(pos: pos + .east, dir: dir, steps: steps + 1)
        case ("-", .west): Cursor(pos: pos + .west, dir: dir, steps: steps + 1)
        case ("L", .west): Cursor(pos: pos + .north, dir: .north, steps: steps + 1)
        case ("L", .south): Cursor(pos: pos + .east, dir: .east, steps: steps + 1)
        case ("J", .east): Cursor(pos: pos + .north, dir: .north, steps: steps + 1)
        case ("J", .south): Cursor(pos: pos + .west, dir: .west, steps: steps + 1)
        case ("7", .east): Cursor(pos: pos + .south, dir: .south, steps: steps + 1)
        case ("7", .north): Cursor(pos: pos + .west, dir: .west, steps: steps + 1)
        case ("F", .north): Cursor(pos: pos + .east, dir: .east, steps: steps + 1)
        case ("F", .west): Cursor(pos: pos + .south, dir: .south, steps: steps + 1)
        default: nil
        }
    }
    static func goOn(start: Pos, dir: Pos, grid: [[Character]]) -> (Cursor, [Pos])? {
        var trace: [Pos] = [start]
        var c = Cursor(pos: start + dir, dir: dir)
        trace.append(c.pos)
        while let next = c.goForward(grid) {
            trace.append(next.pos)
            if next.pos == start {
                return (next, trace)
            }
            c = next
        }
        return nil
    }
}

private func part1(_ grid: [[Character]]) -> (Int, [Pos]) {
    let start: Pos =
        if let (i, s) = grid.enumerated().first(
            where: {
                $0.1.contains("S")
            })
        {
            Pos(y: i, x: s.firstIndex(where: { $0 == "S" })!)
        } else {
            fatalError(#function)
        }
    if let (v, trace) = Cursor.goOn(start: start, dir: .north, grid: grid) {
        return ((v.steps + 1) / 2, trace)
    }
    if let (h, trace) = Cursor.goOn(start: start, dir: .east, grid: grid) {
        return ((h.steps + 1) / 2, trace)
    }
    fatalError()
}

@Model
class Y2023D10State {
    @Attribute(.unique) var name: String
    var val1: Double
    init(name: String, val1: Double) {
        self.name = name
        self.val1 = val1
    }
}

@MainActor
private func part2(_ input: [[Character]], _ trace: [Pos]) -> Int {
    let height = input.count
    let width = input[0].count
    let boundary = Pos(y: (height + 1) * 2, x: (width + 1) * 2)
    // Scale up the grid
    var map2: Set<Pos> = []
    for i in 0..<(trace.count - 1) {
        map2.insert(Pos.unit + trace[i] * 2)
        map2.insert(Pos.unit + trace[i] + trace[i + 1])
    }
    // traverse
    var to_visit: Set<Pos> = [Pos(y: 0, x: 0)]
    while let p = to_visit.popFirst() {
        if map2.contains(p) {
            continue
        }
        map2.insert(p)
        for q in p.neighbors4(bound: boundary) {
            if !map2.contains(q) {
                to_visit.insert(q)
            }
        }
    }
    var count = 0
    for i in 0..<height {
        for j in 0..<width {
            if !map2.contains(Pos(y: 2 * i + 1, x: 2 * j + 1)) {
                count += 1
            }
        }
        print()
    }
    do {
        let container = try ModelContainer(for: Y2023D10State.self)
        let context = container.mainContext
        let state = Y2023D10State(name: "test", val1: Double(count) / Double(height * width))
        context.insert(state)
        try context.save()
    }
    catch {
        print(error)
    }
    return count
}

@MainActor
public func day10(_ data: String) {
    let parser: some Parser<Substring, [[Character]]> = Many {
        Prefix {
            $0 != "\n"
        }.map { Array($0) }
    } separator: {
        "\n"
    }
    do {
        let input = try parser.parse(data).filter { !$0.isEmpty }
        // assert(input.allSatisfy { $0.allSatisfy { $0 != "S" } })
        let (sum1, trace) = part1(input)
        let sum2 = part2(input, trace)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}

struct ContentView: View {
    // @Environment(\.modelContext) private var context
    @Query var data: [Y2023D10State]
    var body: some View {
        VStack {
            Chart {
                BarMark(
                    x: .value("Shape Type", "loaded"),
                    y: .value("Total Count", data[0].val1)
                )
                BarMark(
                    x: .value("Shape Type", "something"),
                    y: .value("Total Count", 1)
                )
            }
            Image(systemName: "globe")
                .imageScale(.large)
                .foregroundStyle(.tint)
            Text("Hello, world!")
        }
        .padding()
    }
}

#Preview {
    ContentView()
        .modelContainer(for: [Y2023D10State.self])
}
