import Parsing

public func day05(_ data: String) {
  let rule_parser = Parse(input: Substring.self) {
    Int.parser()
    "|"
    Int.parser()
  }
  // .map { ($0, $1) }
  let rules_parser = Many { rule_parser } separator: { "\n" }

  let update_parser: some Parser<Substring, [Int]> = Many {
   Int.parser()
  } separator: {
    ","
  }
  let updates_parser: some Parser<Substring, [[Int]]> = Many {
    update_parser
  } separator: {
    "\n"
  }
  let parser = Parse(input: Substring.self) {
    rules_parser
    "\n\n"
    updates_parser
  }
  // .map { (a: [(Int, Int)], b: [Int]) in (a, b) }
  do {
    var input = try parser.parse(data[...])
    input.1 = input.1.filter { !$0.isEmpty }
    print("\(input)")
    let sum1 = 0
    let sum2 = 0
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
  }
  catch {
    print("\(error)")
  }
}
