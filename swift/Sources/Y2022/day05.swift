typealias Tower = [Character]
typealias Move = (Int, Int, Int)

class Towers {
  var tower: [Tower] = []
  init(_ t: [Tower]) {
    tower = t
  }
  func move(_ m: Move) {
    let (n, from, to) = m
    var x = Array(tower[from].prefix(upTo: n))
    tower[from] = Array(tower[from].dropFirst(n))
    x.append(contentsOf: tower[to])
    tower[to] = x
    return
  }
}

public func day05(_ data: String) {
  let block = Array(data.split(separator: "\n\n", omittingEmptySubsequences: false))
  let moves: [Move] = block[1].split(separator: "\n").map {
    let w = $0.split(separator: " ")
    return (Int(w[1])!, Int(w[3])!, Int(w[5])!)
  }
  let s = block[0].split(separator: "\n").map({ Array($0) }).dropLast()
  let width = s[0].count
  var state: [Tower] = Array()
  for i in (Int(0)...width).map({ 1 + 4 * $0 }).filter({ $0 < width }) {
    state.append(s.map({ $0[i] }).filter({ $0 != " " }))
  }
  print(state)
  print(moves)
  func part1(state: [Tower], moves: [Move]) {
    let s = Towers(state)
    for m in moves {
      s.move(m)
    }
    print("Part1: \(state.count)")
  }

  func part2(state: [Tower], moves: [Move]) {
    // var state = state
    print("Part1: \(state.count)")
  }
  part1(state: state, moves: moves)
  part2(state: state, moves: moves)
}
