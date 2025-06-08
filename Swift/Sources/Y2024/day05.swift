import Grape
import Parsing
import SwiftData
import SwiftUI

private func total_order(_ pages: [Int], by rules: [(Int, Int)]) -> [Int] {
    var range = pages
    func swap(to: Int, by rules: [(Int, Int)]) {
        let pivot: Int = range[..<to].partition { p in !rules.contains { p == $0.0 } }
        if pivot == 0 || pivot == to { return }
        if 0 < pivot {
            swap(to: pivot, by: rules.filter { !range[pivot..<to].contains($0.1) })
        }
    }
    swap(to: range.count, by: rules)
    return range
}

private func ordered(_ pages: [Int], by rules: [(Int, Int)]) -> [Int] {
    let rs = rules.filter { pages.contains($0.0) && pages.contains($0.1) }
    return total_order(pages, by: rs)
}

private func part1(_ pages: [Int], by rules: [(Int, Int)]) -> Int {
    if ordered(pages, by: rules) == pages {
        return pages[pages.count / 2]
    } else {
        return 0
    }
}

private func part2(_ pages: [Int], by rules: [(Int, Int)]) -> Int {
    let os = ordered(pages, by: rules)
    if os != pages {
        return os[os.count / 2]
    } else {
        return 0
    }
}

@Model
class Y2024D05Node {
    @Attribute(.unique) var id: Int
    var val: Int
    var size: Double
    init(id: Int, val: Int, size: Double = 4.0) {
        self.id = id
        self.val = val
        self.size = size
    }
}

@Model
class Y2024D05Link {
    @Attribute(.unique) var id: Int
    var pre: Int
    var post: Int
    init(id: Int, pre: Int, post: Int) {
        self.id = id
        self.pre = pre
        self.post = post
    }
}

@Model
class Y2024D05State {
    var nodes: [Y2024D05Node]
    var links: [Y2024D05Link]
    init(nodes: [Y2024D05Node], links: [Y2024D05Link]) {
        self.nodes = nodes
        self.links = links
    }
}

@MainActor
public func day05(_ data: String) {
    let rule_parser: some Parser<Substring, (Int, Int)> = Parse(input: Substring.self) {
        Int.parser()
        "|"
        Int.parser()
    }

    let rules_parser = Many {
        rule_parser
    } separator: {
        "\n"
    }

    let update_parser: some Parser<Substring, [Int]> = Many {
        Int.parser()
    } separator: {
        ","
    }

    let updates_parser: some Parser<Substring, [[Int]]> = Many {
        update_parser
    } separator: {
        "\n"
    }

    let parser: some Parser<Substring, ([(Int, Int)], [[Int]])> = Parse(input: Substring.self) {
        rules_parser
        "\n\n"
        updates_parser
    }

    do {
        let input = try parser.parse(data[...])
        let rules: [(Int, Int)] = input.0
        let updates: [[Int]] = input.1.filter { !$0.isEmpty }
        let sum1 = (updates.map { part1($0, by: rules) }).reduce(0, +)
        let sum2 = (updates.map { part2($0, by: rules) }).reduce(0, +)
        print("Part1: \(sum1)")
        print("Part2: \(sum2)")
        do {
            let c1 = try ModelContainer(for: Y2024D05Node.self)
            try c1.mainContext.delete(model: Y2024D05Node.self)
            let c2 = try ModelContainer(for: Y2024D05Link.self)
            try c2.mainContext.delete(model: Y2024D05Link.self)
        }
        let container = try ModelContainer(for: Y2024D05State.self)
        try container.mainContext.delete(model: Y2024D05State.self)
        let context = container.mainContext
        let pages = Array(Set(rules.flatMap { [$0.0, $0.1] }))
        let pseudoOrderedPages = ordered(pages, by: rules)
        let nodes = pseudoOrderedPages.enumerated().map { (i, n) in
            Y2024D05Node(id: i, val: n, size: 4.0)
        }
        let val2id: [Int: Int] = nodes.reduce(into: [:]) { acc, n in acc[n.val] = n.id }
        let links = rules.enumerated().map { (i, link) in
            Y2024D05Link(id: i, pre: val2id[link.0, default: 0], post: val2id[link.1, default: 0])
        }
        let s = Y2024D05State(nodes: nodes, links: links)
        context.insert(s)
        if context.hasChanges {
            try context.save()
        }
    } catch {
        print("\(error)")
    }
}

private struct GraphView: View {
    var nodes: [Y2024D05Node]
    var links: [Y2024D05Link]
    var body: some View {
        ForceDirectedGraph {
            Series(nodes) { node in
                AnnotationNodeMark(id: node.id, radius: node.size) {
                    Text(String(node.val))
                }
            }
            Series(links) { link in
                LinkMark(from: link.post, to: link.pre)
                    .linkShape(
                        ArrowLineLink(
                            arrowSize: 10,
                            arrowAngle: .degrees(10),
                            arrowCornerRadius: 8.0
                        )
                    )
                    .stroke(.red)
            }
        } force: {
            .manyBody(strength: -80)
                .link(originalLength: 60.0, stiffness: .weightedByDegree { _, _ in 0.9 })
                .center()
        }
    }
}

private struct ContentView: View {
    @Query var store: [Y2024D05State]
    @State var displayNodes: Double = 49
    var body: some View {
        VStack {
            if 0 < store.count {
                VStack {
                    GraphView(
                        nodes: Array(
                            store.first!.nodes.filter { node in node.id < Int(displayNodes) }
                        ),
                        links: Array(
                            store.first!.links.filter { link in
                                link.post < Int(displayNodes) && link.pre < Int(displayNodes)
                            }
                        )
                    )
                    .padding()
                    Slider(
                        value: $displayNodes,
                        in: 2...Double(store.first!.nodes.count),
                        label: { Text("Number of pages \(Int(displayNodes))") },
                        minimumValueLabel: { Text("single") },
                        maximumValueLabel: { Text("all (\(store.first!.nodes.count))") },
                    )
                    .padding(.horizontal)
                    .padding(.bottom)
                }
            } else {
                Text("no data")
            }
        }

    }
}

#Preview {
    ContentView()
        .modelContainer(for: Y2024D05State.self)
}
