fileprivate struct Dim2: Comparable, Hashable {
  let y: Int
  let x: Int
  // Implement the Comparable operators
  static func == (lhs: Dim2, rhs: Dim2) -> Bool {
    return lhs.y == rhs.y && lhs.x == rhs.x
  }
  static func < (lhs: Dim2, rhs: Dim2) -> Bool {
    return lhs.y < rhs.y || (lhs.y == rhs.y && lhs.x < rhs.x)
  }
  func inc(_ other: Dim2) -> Dim2 { Dim2(y: y + other.y, x: x + other.x) }
  func scale(_ s: Int) -> Dim2 { Dim2(y: y * s, x: x * s) }
  func move(as_next base: Dim2) -> Dim2 {
    func signum (_ x: Int) -> Int {
      if x < 0 { -1
      } else if x == 0 { 0
      } else { 1 }
    }
    let diff_y = base.y - y
    let diff_x = base.x - x
    if 2 <= max(abs(diff_y), abs(diff_x)) {
      return Dim2(y: y + signum(diff_y), x: x + signum(diff_x))
    } else {
      return self
    }
  }
}

private struct Move {
  let dir: Dim2
  let len: Int
  init(_ s: String) {
    len = Int(s.dropFirst(2))!
    dir = switch s.first! {
      case "U": Dim2(y: -1, x: 0)
      case "D": Dim2(y: 1, x: 0)
      case "L": Dim2(y: 0, x: -1)
      case "R": Dim2(y: 0, x: 1)
      default: fatalError()
    }
  }
  var vector: Dim2 {
    get { dir.scale(len) }
  }
}

public func day09(_ data: String) {
  let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
  let moves: [Move] = lines.map { return Move(String($0)) }
  func solve(_ moves: [Move], length len: Int, part: Int) {
    var rope: [Dim2] = [Dim2(y: 0, x: 0)]
    var map: Set<Dim2> = []
    for _ in 1..<len { rope.append(Dim2(y: 0, x: 0)) }
    for m in moves {
      let vec = m.dir
      for _ in 0..<m.len {
        rope[0] = rope[0].inc(vec)
        for tail in 1..<len {
          rope[tail] = rope[tail].move(as_next: rope[tail - 1])
        }
        map.insert(rope[len - 1])
      }
    }
    print("Part\(part): \(map.count)")
  }
  solve(moves, length: 2, part: 1)
  solve(moves, length: 10, part: 2)
}
