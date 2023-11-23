public func day04(_ data: String) {
  typealias R = (Int, Int)
  let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
  let inputs = lines.map {
    let a = Array($0.split(separator: ",")).map {
      let a = Array($0.split(separator: "-")).map {
        Int($0)!
      }
      return (a[0], a[1])
    }
    return (a[0], a[1])
  }
  func part1(_ lines: [(R, R)]) {
    let sum = lines.filter { l in
      return (l.0.0 <= l.1.0 && l.1.1 <= l.0.1) || (l.1.0 <= l.0.0 && l.0.1 <= l.1.1)
    }.count
    print("Part1: \(sum)")
  }

  func part2(_ lines: [(R, R)]) {
    let sum = lines.filter { l in
      return (l.0.0 <= l.1.0 && l.1.0 <= l.0.1) || (l.1.0 <= l.0.0 && l.0.0 <= l.1.1)
    }.count
    print("Part2: \(sum)")
  }
  part1(inputs)
  part2(inputs)
}
