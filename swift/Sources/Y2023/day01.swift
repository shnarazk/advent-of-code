public func day01(_ data: String) {
  let c = data.split(separator: "\n", omittingEmptySubsequences: false).split(separator: [])
  print("Part1: \(c)")
  print("Part2: \(c.count)")
}
