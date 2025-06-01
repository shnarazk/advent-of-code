import Parsing

private func part1() -> Int {
    0
}

private func part2() -> Int {
    0
}

public func day(_ data: String) {
    do {
        let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        let sum1 = part1(cards)
        let sum2 = part2(cards)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
