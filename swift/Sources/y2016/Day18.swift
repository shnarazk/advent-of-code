import Foundation

public func day18(_ data: String) {
  var line = [false]
  line.append(contentsOf: data.trimmingCharacters(in: CharacterSet.newlines).map { $0 == "^" })
  line.append(false)
  count(line: line, to: 40, label: 1)
  count(line: line, to: 400000, label: 2)
}

func count(line: [Bool], to: Int, label: Int) {
  var line = line
  var safes: Int = countSafe(in: line)
  func newGeneration(from: [Bool]) -> [Bool] {
    var to: [Bool] = [false]
    to.append(contentsOf: (1..<from.count - 1).map { from[$0 - 1] != from[$0 + 1] })
    to.append(false)
    return to
  }
  func countSafe(in vec: [Bool]) -> Int { vec.filter({ !$0 }).count - 2 }
  for _ in 1..<to {
    line = newGeneration(from: line)
    safes += countSafe(in: line)
  }
  print("Part\(label): \(safes)")
}
