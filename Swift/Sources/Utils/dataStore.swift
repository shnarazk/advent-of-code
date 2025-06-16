//
//  dataStore.swift
//  aoc
//
//  Created by 楢崎修二 on 6/16/25.
//
import Foundation
import SwiftData

public func getAoCModelConfiguration() -> ModelConfiguration {
    let appGroupID = "group.com.yourdomain.sharedgroup"
    let containerURL = FileManager.default.containerURL(forSecurityApplicationGroupIdentifier: appGroupID)!
    let storeURL = containerURL.appendingPathComponent("AdventOfCode.sqlite")
    if #available(macOS 15, *) {
        return ModelConfiguration(url: storeURL)
    } else {
        // Fallback on earlier versions
        fatalError()
    }
}

