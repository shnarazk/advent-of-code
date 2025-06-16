import Charts
//
//  day14.swift
//  aoc
//
import Parsing
import SwiftData
import SwiftUI
import Utils

@DebugDescription
private struct Robot {
    let pos: Pos
    let vec: Pos
    var debugDescription: String {
        "(\(pos.y): \(pos.x)) (\(vec.y), \(vec.x))"
    }
}

private func part1(robots: [Robot], boundary: Pos) -> Int {
    let time = 100
    let map =
        robots
        // map to the final positions
        .map {
            ((($0.vec * time + $0.pos) % boundary) + boundary) % boundary
        }
        // map to region map
        .reduce((0, 0, 0, 0)) {
            if boundary.y / 2 == $1.y || boundary.x / 2 == $1.x {
                $0
            } else {
                switch (boundary.y / 2 < $1.y, boundary.x / 2 < $1.x) {
                case (false, false): ($0.0 + 1, $0.1, $0.2, $0.3)
                case (false, true): ($0.0, $0.1 + 1, $0.2, $0.3)
                case (true, false): ($0.0, $0.1, $0.2 + 1, $0.3)
                case (true, true): ($0.0, $0.1, $0.2, $0.3 + 1)
                }
            }
        }
    // convert to the product
    return map.0 * map.1 * map.2 * map.3
}

@Model
public class Y2024D14State {
    @Attribute(.unique) var time: Int
    var rate: Double
    var isMax: Bool = false
    init(time: Int, rate: Double, isMax: Bool) {
        self.time = time
        self.rate = rate
        self.isMax = isMax
    }
}

@MainActor
private func part2(robots: [Robot], boundary: Pos) -> Int {
    let decayRate = 0.95
    let numPoints = Double(robots.count)
    var signalRateEMA = 1.0
    var peakMax: Double = 0
    var peakMin: Double = 10.0
    do {
        let container: ModelContainer = {
            let config = getAoCModelConfiguration()
            return try! ModelContainer(for: Y2024D14State.self, configurations: config)
        }()
        // let container = try ModelContainer(for: Y2024D14State.self)
        let context = container.mainContext

        for t in 0... {
            let map =
                Set(
                    robots
                        .map {
                            ((($0.vec * t + $0.pos) % boundary) + boundary) % boundary
                        }
                )
            let numConnected = map.filter {
                !$0.neighbors4(bound: boundary).allSatisfy { !map.contains($0) }
            }.count
            let r = Double(numConnected) / numPoints
            let trend = r / signalRateEMA
            if peakMax < trend {
                peakMax = trend
                context.insert(Y2024D14State(time: t, rate: trend, isMax: true))
                try context.save()
            }
            if r / peakMax < peakMin {
                peakMin = r / peakMax
                context.insert(Y2024D14State(time: t, rate: trend, isMax: false))
                try context.save()
            }
            if 3.0 < r / signalRateEMA {
                return t
            }
            signalRateEMA *= decayRate
            signalRateEMA += r * (1.0 - decayRate)
        }
        fatalError()
    } catch {
        print(error)
        fatalError()
    }
}

@MainActor public func day14(_ data: String) {
    let is_test = Array(data.split(separator: "\n", omittingEmptySubsequences: true)).count == 12
    let boundary: Pos = is_test ? Pos(y: 7, x: 11) : Pos(y: 103, x: 101)
    let robot: some Parser<Substring, Robot> = Parse {
        "p="
        Int.parser()
        ","
        Int.parser()
        " v="
        Int.parser()
        ","
        Int.parser()
    }.map { Robot(pos: Pos(y: $1, x: $0), vec: Pos(y: $3, x: $2)) }
    let parser: some Parser<Substring, [Robot]> = Many {
        robot
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    do {
        let input = try parser.parse(data)
        let sum1 = part1(robots: input, boundary: boundary)
        let sum2 = part2(robots: input, boundary: boundary)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}

public struct Y2024Day14View: View {
    @Query public var data: [Y2024D14State]
    public init() {}
    public var body: some View {
        VStack {
            Chart(data, id: \.time) {
                PointMark(
                    x: .value("Steps", $0.time),
                    y: .value("Signal ratio", $0.rate)
                )
                .foregroundStyle(by: .value("Family", $0.isMax ? "max" : "min"))
            }
            .chartXAxis {
                AxisMarks(values: .automatic(desiredCount: 7))
            }
            .chartYAxis {
                AxisMarks(values: .automatic(desiredCount: 5))
            }

            Text("Step-Peak signal ratio")
        }
        .padding()
    }
}

#Preview {
    let container: ModelContainer = {
        let config = getAoCModelConfiguration()
        return try! ModelContainer(for: Y2024D14State.self, configurations: config)
    }()
    Y2024Day14View()
        .modelContainer(container)
}
