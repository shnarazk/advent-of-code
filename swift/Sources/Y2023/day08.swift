public func day08(_ data: String) {
  let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
  let select: [Character] = Array(lines.first!)
  let tree: [String: (String, String)] = Dictionary(
    uniqueKeysWithValues: lines.dropFirst().map({
      let i1 = $0.index($0.startIndex, offsetBy: 7)
      let i2 = $0.index($0.startIndex, offsetBy: 10)
      let i3 = $0.index($0.startIndex, offsetBy: 12)
      let i4 = $0.index($0.startIndex, offsetBy: 15)
      return (String($0.prefix(3)), (String($0[i1..<i2]), String($0[i3..<i4])))
    }))
  func part1() {
    var pos = "AAA"
    var i = 0
    var steps = 0
    while pos != "ZZZ" {
      pos = if select[i] == "L" { tree[pos]!.0 } else { tree[pos]!.1 }
      steps += 1
      i += 1
      if i == select.count {
        i = 0
      }
    }
    print("Part1: \(steps)")
  }

  func part2() {
    print("Part2: \(tree.count)")
  }
  part1()
  part2()
}
