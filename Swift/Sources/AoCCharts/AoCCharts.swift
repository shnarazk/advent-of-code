//
//  SwiftUIView.swift
//  aoc
//
import SwiftData
import SwiftUI
import Utils
import Y2024

@MainActor
@main
struct AoCCharts: App {
    private let container: ModelContainer = {
        let config = getAoCModelConfiguration()
        return try! ModelContainer(for: Y2024D14State.self, configurations: config)
    }()
    var body: some Scene {
        WindowGroup {
            Y2024Day14View()
                .modelContainer(container)
        }
    }
}

//#Preview {
//    AoCCharts()
//}
