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
    let starts = tree.keys.filter({ $0.last == "A"})
    var ans = 1
    for start in starts {
      var pos = start
      var i = 0
      var steps = 0
      while pos.last != "Z" {
        pos = if select[i] == "L" { tree[pos]!.0 } else { tree[pos]!.1 }
        steps += 1
        i += 1
        if i == select.count {
          i = 0
        }
      }
      ans = lcm(ans, steps)
    }
    print("Part2: \(ans)")
  }
  part1()
  part2()
}

func gcd(_ a: Int, _ b: Int) -> Int {
    return b == 0 ? a : gcd(b, a % b)
}

func lcm(_ a: Int, _ b: Int) -> Int {
    if a == 0 || b == 0 {
        return 0
    }
    return abs(a * b) / gcd(a, b)
}
