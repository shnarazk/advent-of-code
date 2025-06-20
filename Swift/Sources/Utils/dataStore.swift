//
//  dataStore.swift
//  aoc
//
import Foundation
import SwiftData

@Model
public class AoCDescription {
    @Attribute(.unique) public var aocId: String
    public var year: Int
    public var day: Int
    public var variant: String? = nil
    public var text: String
    public var desc: String = ""
    public var answer1: String?
    public var answer2: String?
    public init(year: Int, day: Int, variant: String?, text: String, desc: String = "") {
        let d = String(format: "%02d", day)
        let v = if let variant { "-\(variant)" } else { "" }
        self.aocId = "\(year)-\(d)\(v)"
        self.year = year
        self.day = day
        self.variant = variant
        self.text = text
        self.desc = desc
        self.answer1 = nil
        self.answer1 = nil
    }
}

/// Save the text to the storage
@MainActor
public func saveDescription(
    year: Int,
    day: Int,
    variant: String?,
    text: String,
    force: Bool = false
) {
    do {
        let puzzle = AoCDescription(year: year, day: day, variant: variant, text: text)
        let config = getAoCModelConfiguration()
        let container = try! ModelContainer(for: AoCDescription.self, configurations: config)
        let context = container.mainContext
        var descriptor = FetchDescriptor<AoCDescription>(
            predicate: #Predicate { $0.year == year && $0.day == day && $0.variant == variant },
            sortBy: [.init(\.answer1)]
        )
        descriptor.fetchLimit = 10
        let exists = try context.fetch(descriptor)
        if let data = exists.first {
            if force {
                data.text = text
                try context.save()
            }
        } else {
            context.insert(puzzle)
            try context.save()
        }
    } catch {
        print(error)
        fatalError()
    }
}

public func getAoCModelConfiguration() -> ModelConfiguration {
    let appGroupID = "com.shnarazk.sharedgroup.aoc"
    let containerURL = FileManager.default.containerURL(
        forSecurityApplicationGroupIdentifier: appGroupID
    )!
    let storeURL = containerURL.appendingPathComponent("AdventOfCode.sqlite")
    if #available(macOS 15, *) {
        return ModelConfiguration(url: storeURL)
    } else {
        // Fallback on earlier versions
        fatalError()
    }
}
