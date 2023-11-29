fileprivate typealias Dim2 = (Int, Int)

fileprivate func inc (_ lhs: Dim2, _ rhs: Dim2) -> Dim2 {
  (lhs.0 + rhs.0, lhs.1 + rhs.1)
}
fileprivate func move_next(_ next: Dim2, of base: Dim2) -> Dim2 {
  func signum (_ x: Int) -> Int {
    if x < 0 {
      -1
    } else if x == 0 {
      0
    } else {
      1
    }
  }
  let diff_y = next.0 - base.0
  let diff_x = next.1 - base.1
  if 2 <= abs(diff_y) + abs(diff_x) {
    return (next.0 + signum(diff_y), next.1 + signum(diff_x))
  } else {
    return next
  }
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
  var vector: Dim2 {
    get {
      (dir.0 * len, dir.1 * len)
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
      rope[0] = inc(rope[0], m.vector)
      for tail in 1..<len {
        rope[tail] = move_next(rope[tail], of: rope[tail - 1])
      }
    }
    print("Part\(part): \(rope.last!)")
  }
  part(moves, length: 2, part: 1)
  part(moves, length: 10, part: 2)
}
