typealias Tower = [Character]
typealias Move = (Int, Int, Int)

class Towers {
  var tower: [Tower] = []
  init(_ t: [Tower]) {
    tower = t
  }
  func move(_ m: Move, flip: Bool) {
    var (n, from, to) = m
    from -= 1
    to -= 1
    var x = Array(tower[from].prefix(upTo: n))
    tower[from] = Array(tower[from].dropFirst(n))
    if flip {
      x.reverse()
    }
    x.append(contentsOf: tower[to])
    tower[to] = x
  }
  func tops() -> String {
    return String(tower.map({ $0.first! }))
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
  func part(state: [Tower], moves: [Move], part: Int) {
    let s = Towers(state)
    moves.forEach { s.move($0, flip: part == 1) }
    print("Part1: \(s.tops())")
  }
  part(state: state, moves: moves, part: 1)
  part(state: state, moves: moves, part: 2)
}
