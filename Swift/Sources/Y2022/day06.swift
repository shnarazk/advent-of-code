public func day06(_ data: String) {
  func part(_ line: String, windows: Int) {
    let l = Array(line)
    for i in 0...l.count - windows {
      var bag: Set<Character> = Set()
      for j in 0..<windows { bag.insert(l[i + j]) }
      if bag.count == windows {
        print("Part1: \(i + windows)")
        return
      }
    }
  }
  part(data, windows: 4)
  part(data, windows: 14)
}
