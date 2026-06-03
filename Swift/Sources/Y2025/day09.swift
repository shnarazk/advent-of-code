import Parsing

private func part1(_ input: [(Int, Int)]) -> Int {
    input.indices.map { i in
        input.indices.dropFirst(i + 1).map { j in
            abs(input[i].0 - input[j].0 + 1) * abs(input[i].1 - input[j].1 + 1)
        }.reduce(0, max)
    }.reduce(0, max)
}

private func part2(_ line: [(Int, Int)]) -> Int {
    // Coordinate compression: collect unique y/x values, add 0, sort, encode to indices
    var ys = Array(Set(line.map { $0.0 }))
    ys.append(0)
    ys.sort()
    var encodeY: [Int: Int] = [:]
    for (e, d) in ys.enumerated() { encodeY[d] = e }

    var xs = Array(Set(line.map { $0.1 }))
    xs.append(0)
    xs.sort()
    var encodeX: [Int: Int] = [:]
    for (e, d) in xs.enumerated() { encodeX[d] = e }

    // Group x-values by y (horizontal segments) and y-values by x (vertical segments)
    var sliceY: [Int: [Int]] = [:]
    var sliceX: [Int: [Int]] = [:]
    for p in line {
        sliceY[p.0, default: []].append(p.1)
        sliceX[p.1, default: []].append(p.0)
    }
    for key in sliceY.keys { sliceY[key]!.sort() }
    for key in sliceX.keys { sliceX[key]!.sort() }

    // Build compressed grid: 1 = wall, 2 = inside, 3 = unvisited (potential exterior)
    let gridSize = ys.count + 2
    var grid = [[Int]](repeating: [Int](repeating: 3, count: gridSize), count: gridSize)
    for (y, xPair) in sliceY {
        let ey = encodeY[y]!
        let ex0 = encodeX[xPair[0]]!
        let ex1 = encodeX[xPair[1]]!
        grid[ey][ex0] = 1
        grid[ey][ex1] = 1
        for x in (ex0 + 1)..<ex1 { grid[ey][x] = 2 }
    }
    for (x, yPair) in sliceX {
        let ex = encodeX[x]!
        let ey0 = encodeY[yPair[0]]!
        let ey1 = encodeY[yPair[1]]!
        for row in (ey0 + 1)..<ey1 { grid[row][ex] = 2 }
    }

    // Flood fill from (0,0) with 8-connectivity to mark true exterior as 0
    var toVisit: [(Int, Int)] = [(0, 0)]
    while let p = toVisit.popLast() {
        if grid[p.0][p.1] == 3 {
            grid[p.0][p.1] = 0
            for dy in -1...1 {
                for dx in -1...1 {
                    if dy == 0 && dx == 0 { continue }
                    let ny = p.0 + dy
                    let nx = p.1 + dx
                    if (0..<gridSize).contains(ny) && (0..<gridSize).contains(nx)
                        && grid[ny][nx] == 3
                    {
                        toVisit.append((ny, nx))
                    }
                }
            }
        }
    }
    // Any remaining 3s are enclosed — mark as 2
    for i in grid.indices {
        for j in grid[i].indices { if grid[i][j] == 3 { grid[i][j] = 2 } }
    }

    // Find maximum rectangle area anchored at each wall cell
    var area = 0
    for by in 1..<gridSize {
        for bx in 1..<gridSize {
            if grid[by][bx] != 1 { continue }
            var minX = 0
            for y in by..<gridSize {
                if minX <= bx {
                    for x in (minX...bx).reversed() {
                        if grid[y][x] == 0 {
                            minX = x + 1
                            break
                        }
                        if grid[y][x] == 1 {
                            area = max(area, (abs(ys[by] - ys[y]) + 1) * (abs(xs[bx] - xs[x]) + 1))
                        }
                    }
                }
            }
            var maxX = gridSize
            for y in by..<gridSize {
                for x in bx..<maxX {
                    if grid[y][x] == 0 {
                        maxX = x
                        break
                    }
                    if grid[y][x] == 1 {
                        area = max(area, (abs(ys[by] - ys[y]) + 1) * (abs(xs[bx] - xs[x]) + 1))
                    }
                }
            }
        }
    }
    return area
}

public func day09(_ data: String) throws {
    let line_parser: some Parser<Substring, (Int, Int)> = Parse {
        Int.parser()
        ","
        Int.parser()
        "\n"
    }
    let parser: some Parser<Substring, [(Int, Int)]> = Many {
        line_parser
    }
    let input = try parser.parse(data)
    let sum1 = part1(input)
    let sum2 = part2(input)
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
