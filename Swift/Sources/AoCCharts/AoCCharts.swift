//
//  SwiftUIView.swift
//  aoc
//
import SwiftData
import SwiftUI
import Utils
import Y2023
import Y2024

@available(macOS 26.0, *)
@MainActor
@main
struct AoCChartsApp: App {
    var body: some Scene {
        WindowGroup {
            AoCCharts()
        }
    }
}

struct AoCCharts: View {
    private let modelConf: ModelConfiguration = getAoCModelConfiguration()
    var body: some View {
            NavigationSplitView {
                List {
                    Section(header: Text("y2024")) {
                        NavigationLink {
                            Y2024Day14View()
                                .modelContainer(
                                    try! ModelContainer(
                                        for: Y2024D14State.self,
                                        configurations: modelConf
                                    )
                                )
                        } label: {
                            Text("day14")
                        }
                        NavigationLink {
                            Text("ok")
                        } label: {
                            Text("WIP")
                        }
                    }
                    Section(header: Text("2023")) {
                        NavigationLink {
                            Y2023Day10View()
                                .modelContainer(
                                    try! ModelContainer(
                                        for: Y2023D10State.self,
                                        configurations: modelConf
                                    )
                                )
                        } label: {
                            Text("day10")
                        }
                        NavigationLink {

                        } label: {
                            Text("WIP")
                        }
                    }
                }
            } detail: {
            }
        }
    }

#Preview {
    AoCCharts()
}
