// swift-tools-version: 6.2
// The swift-tools-version declares the minimum version of Swift required to build this package.

import PackageDescription

let package = Package(
    name: "aoc",
    platforms: [.macOS(.v26)],
    dependencies: [
        .package(
            url: "https://github.com/apple/swift-argument-parser",
            .upToNextMinor(from: "1.0.0")
        ),
        .package(
            url: "https://github.com/apple/swift-collections.git",
            .upToNextMinor(from: "1.2.0")
        ),
        .package(
            url: "https://github.com/pointfreeco/swift-parsing",
            .upToNextMinor(from: "0.14.0")
        ),
        .package(
            url: "https://github.com/swiftgraphs/Grape",
            .upToNextMinor(from: "1.1.0")
        ),
    ],
    targets: [
        // Targets are the basic building blocks of a package, defining a module or a test suite.
        // Targets can depend on other targets in this package and products from dependencies.
        .executableTarget(
            name: "aoc",
            dependencies: [
                .product(
                    name: "ArgumentParser",
                    package: "swift-argument-parser"
                ),
                .product(name: "Collections", package: "swift-collections"),
                .target(name: "Utils"),
                .target(name: "Y2016"),
                .target(name: "Y2022"),
                .target(name: "Y2023"),
                .target(name: "Y2024"),
                .target(name: "Y2025"),
            ],
            //            swiftSettings: [
            //                .unsafeFlags(["-Xfrontend", "-enable-debug-dylib"])
            //            ]
        ),
        .executableTarget(
            name: "AoCCharts",
            dependencies: [
                .product(name: "Collections", package: "swift-collections"),
                .target(name: "Utils"),
                .target(name: "Y2016"),
                .target(name: "Y2022"),
                .target(name: "Y2023"),
                .target(name: "Y2024"),
                .target(name: "Y2025"),
            ],
        ),
        .executableTarget(
            name: "parser1",
            dependencies: [
                .product(
                    name: "ArgumentParser",
                    package: "swift-argument-parser"
                ),
                .product(name: "Collections", package: "swift-collections"),
                .product(name: "Parsing", package: "swift-parsing"),
            ]
        ),
        .target(name: "Utils", dependencies: []),
        .target(
            name: "Y2025",
            dependencies: [
                .product(name: "Parsing", package: "swift-parsing"),
                .product(name: "Collections", package: "swift-collections"),
                .product(name: "Grape", package: "Grape"),
                .target(name: "Utils"),
            ]
        ),
        .target(
            name: "Y2024",
            dependencies: [
                .product(name: "Parsing", package: "swift-parsing"),
                .product(name: "Collections", package: "swift-collections"),
                .product(name: "Grape", package: "Grape"),
                .target(name: "Utils"),
            ]
        ),
        .target(
            name: "Y2023",
            dependencies: [
                .product(name: "Parsing", package: "swift-parsing"),
                .product(name: "Collections", package: "swift-collections"),
                .target(name: "Utils"),
            ]
        ),
        .target(
            name: "Y2022",
            dependencies: [
                .product(name: "Parsing", package: "swift-parsing"),
                .product(name: "Collections", package: "swift-collections"),
                .target(name: "Utils"),
            ]
        ),
        .target(name: "Y2016", dependencies: []),
        .testTarget(
            name: "aoc-test",
            dependencies: [
                .product(
                    name: "ArgumentParser",
                    package: "swift-argument-parser"
                ),
                .product(name: "Collections", package: "swift-collections"),
                .product(name: "Parsing", package: "swift-parsing"),
                .target(name: "Utils"),
                .target(name: "Y2024"),
                .target(name: "Y2023"),
            ]
        ),
    ]
)
