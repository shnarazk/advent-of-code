private struct Move {
  let dir: (Int, Int)
  let len: Int
  init(_ s: String) {
    len = Int(s.dropFirst(2))!
    dir = switch s.first! {
      case "U": (-1, 0)
      case "D": (1, 0)
      case "L": (0, -1)
      case "R": (0, 1)
      default: fatalError()
    }
  }
}

public func day09(_ data: String) {
  let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
  let moves: [Move] = lines.map { return Move(String($0)) }
  func part1(_ moves: [Move]) {
    print("Part1: \(moves.count)")
  }
  func part2(_ moves: [Move]) {
    print("Part2: \(moves.count)")
  }
  part1(moves)
  part2(moves)
}
