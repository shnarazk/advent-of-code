public func day01(_ data: String) {
  let c = data.split(separator: "\n", omittingEmptySubsequences: true)
  var sum1 = 0
  var sum2 = 0
  for line in c {
    let b = Array(line.filter({ $0.isNumber }))
    sum1 += Int(String([b[0], b[b.count - 1]]))!
    let a = Array(line)
    var v: [Character] = []
    let digit = [
      ("one", "1"),
      ("two", "2"),
      ("three", "3"),
      ("four", "4"),
      ("five", "5"),
      ("six", "6"),
      ("seven", "7"),
      ("eight", "8"),
      ("nine", "9"),
    ]
    for i in 0..<a.count {
      if a[i].isNumber {
        v.append(a[i])
        continue
      }
      let target = line.dropFirst(i)
      for (s, n) in digit {
        if target.starts(with: s) {
          v.append(n.first!)
        }
      }
    }
    sum2 += Int(String([v[0], v[v.count - 1]]))!
  }
  print("Part1: \(sum1)")
  print("Part2: \(sum2)")
}
