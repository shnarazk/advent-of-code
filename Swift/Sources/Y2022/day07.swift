//
//  day07.swift
//  aoc
//

import Parsing

private enum DirEntry {
    case file(String, Int)
    case dir(String)
}

private enum CmdOutput {
    case cdRoot
    case cdParent
    case cd(String)
    case ls([DirEntry])
}

private func part1() -> Int {
    0
}

private func part2() -> Int {
    0
}

public func day07(_ data: String) {
    let ls_output: some Parser<Substring, DirEntry> = OneOf {
        Parse {
            "dir "
            Prefix {
                $0 != "\n"
            }
        }.map { .dir(String($0)) }
        Parse {
            Int.parser()
            " "
            Prefix {
                $0 != "\n"
            }
        }.map { .file(String($1), $0) }
    }
    let cmd: some Parser<Substring, CmdOutput> = OneOf {
        Parse {
            "$ cd /"
        }.map { _ in .cdRoot }
        Parse {
            "$ cd .."
        }.map { _ in .cdParent }
        Parse {
            "$ cd "
            Prefix {
                $0 != "\n"
            }
        }.map { .cd(String($0)) }
        Parse {
            "$ ls\n"
            Many {
                ls_output
            } separator: {
                "\n"
            }
        }.map { .ls($0) }
    }
    let parser: some Parser<Substring, [CmdOutput]> = Many {
        cmd
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    do {
        let input = try parser.parse(data)
        let sum1 = part1()
        let sum2 = part2()
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
