//
//  SwiftUIView.swift
//  aoc
//
import SwiftData
import SwiftUI
import Utils
import Y2024

enum TargetGraph {
    case Y2025Day14
}

@available(macOS 26.0, *)
@MainActor
@main
struct AoCCharts: App {
    private let container: ModelContainer = {
        let config = getAoCModelConfiguration()
        return try! ModelContainer(for: Y2024D14State.self, configurations: config)
    }()
    @State private var targetGrsph: TargetGraph = .Y2025Day14
    var body: some Scene {
        WindowGroup {
            NavigationSplitView {
                List {
                    Section(header: Text("y2024")) {
                        Text("day14")
                    }
                }
            } detail: {
                switch targetGrsph {
                case .Y2025Day14:
                    Y2024Day14View()
                        .modelContainer(container)
                }

            }
        }
    }
}

//#Preview {
//    AoCCharts()
//}
