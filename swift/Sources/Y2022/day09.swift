fileprivate typealias Dim2 = (Int, Int)

func inc (_ lhs: (Int, Int), _ rhs: (Int, Int)) -> (Int, Int) {
  (lhs.0 + rhs.0, lhs.1 + rhs.1)
}

private struct Move {
  let dir: Dim2
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
  func part(_ moves: [Move], length len: Int, part: Int) {
    var rope: [Dim2] = [(0, 0)]
    for _ in 1..<len { rope.append((0, 0)) }
    for m in moves {
      rope[0] = inc(rope[0], m.dir)
      for tail in 1..<len {
        rope[tail] = inc(rope[tail], m.dir) // FIXME: revise
      }
    }
    print("Part\(part): \(rope.last!)")
  }
  part(moves, length: 2, part: 1)
  part(moves, length: 10, part: 2)
}
