typealias Matrix = [[Int]]
public func day08(_ data: String) {
  let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
  let m = lines.map({ Array($0.map({ Int(String($0))! })) })
  func horizontal_segments(x: Int, y: Int) -> ([Int], [Int]) {
    return ((0..<x).map({ m[y][$0] }), (x + 1..<m.count).map({ m[y][$0] }))
  }
  func vertical_segments(x: Int, y: Int) -> ([Int], [Int]) {
    return ((0..<y).map({ m[$0][x] }), (y + 1..<m[0].count).map({ m[$0][x] }))
  }
  func visible(x: Int, y: Int) -> Bool {
    let (up, down) = vertical_segments(x: x, y: y)
    let (left, right) = horizontal_segments(x: x, y: y)
    let base = m[y][x]
    return ![up, down, left, right].allSatisfy({ !$0.allSatisfy({ $0 < base }) })
  }
  func watchable(x: Int, y: Int) -> Int {
    let (up, down) = vertical_segments(x: x, y: y)
    let (left, right) = horizontal_segments(x: x, y: y)
    let base = m[y][x]
    return [up.reversed(), down, left.reversed(), right].map({
      var len = 0
      for t in $0 {
        len += 1
        if base <= t { return len }
      }
      return len
    }).reduce(1) { $0 * $1 }
  }
  func part1(_ m: Matrix) {
    let x = (0..<m.count).map({ (y) in (0..<m[0].count).filter({ visible(x: $0, y: y) }).count })
      .reduce(0) { $0 + $1 }
    print("Part1: \(x)")
  }

  func part2(_ m: Matrix) {
    let x = (0..<m.count).map({
      (y) in (0..<m[0].count).map({ watchable(x: $0, y: y) }).reduce(0) { max($0, $1) }
    })
    .reduce(0) { max($0, $1) }
    print("Part2: \(x)")
  }
  part1(m)
  part2(m)
}
