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

private enum FileSystemKind {
    case file
    case dir
}

private protocol FileSystem {
    var size: Int { get }
    var size1: Int { get }
    var kind: FileSystemKind { get }
    func cd(path: ArraySlice<String>) -> FileSystemDir?
    func traverse<T>(_ map: (FileSystemDir) -> T) -> [[String]: T]
}

@DebugDescription
private class FileSystemFile: FileSystem {
    var size: Int
    init(size: Int) {
        self.size = size
    }
    var debugDescription: String {
        "File(\(size))"
    }
    var size1: Int { 0 }
    var kind: FileSystemKind { .file }
    func cd(path: ArraySlice<String>) -> FileSystemDir? {
        nil
    }
    func traverse<T>(_ map: (FileSystemDir) -> T) -> [[String]: T] {
        [:]
    }
}

@DebugDescription
private class FileSystemDir: FileSystem {
    var entries: [String: FileSystem] = [:]
    var kind: FileSystemKind { .dir }
    var size: Int {
        entries.values.reduce(0) { $0 + $1.size }
    }
    var size1: Int {
        let subs = entries.values.reduce(0) { $0 + $1.size1 }
        return subs + (size < 100000 ? size : 0)
    }
    var debugDescription: String {
        "Dir(\(entries.keys))"
    }
    func addFile(name: String, size: Int) {
        entries[name] = FileSystemFile(size: size)
    }
    func addDirectory(name: String) {
        entries[name] = FileSystemDir()
    }
    func cd(path: ArraySlice<String>) -> FileSystemDir? {
        guard let dirname = path.first else { return self }
        guard let d = entries[dirname] else { fatalError() }
        return d.cd(path: path.dropFirst())
    }
    func traverse<T>(_ map: (FileSystemDir) -> T) -> [[String]: T] {
        var s: [[String]: T] = entries.reduce(into: [:]) { dict, entry in
            for res in entry.value.traverse(map) {
                dict[[entry.key] + res.key] = res.value
            }
        }
        s[[]] = map(self)
        return s
    }
}

private func buildFileSystem(_ input: [CmdOutput]) -> FileSystemDir {
    let root = FileSystemDir()
    var pwd: [String] = []
    for cmd in input {
        switch cmd {
        case .cdRoot: pwd = []
        case .cdParent: pwd.removeLast()
        case .cd(let dirname): pwd.append(dirname)
        case .ls(let entries):
            guard let dir = root.cd(path: pwd[...]) else {
                fatalError()
            }
            for entry in entries {
                switch entry {
                case .file(let name, let size):
                    dir.addFile(name: name, size: size)
                case .dir(let name):
                    dir.addDirectory(name: name)
                }
            }
        }
    }
    return root
}

private func part1(_ root: FileSystemDir) -> Int {
    root.size1
}

private func part2(_ root: FileSystem) -> Int {
    let used = root.size
    let x = root.traverse { $0.size }.map { $0.value }
    let target = x.filter { 70_000_000 - (used - $0) >= 30_000_000 }.min()!
    return target
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
        let fs = buildFileSystem(input)
        let sum1 = part1(fs)
        let sum2 = part2(fs)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
