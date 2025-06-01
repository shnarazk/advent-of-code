//
//  math.swift
//  aoc
//

/// Append two Ints
///
/// ## example
///
/// ```swift
/// append_digits(234, 67) => 23467
/// ```
public func append_digits(_ a: Int, _ b: Int) -> Int {
    func step(_ n: Int, _ x: Int) -> Int {
        if x < 10 {
            return n * 10 + b
        }
        return step(n * 10, x / 10)
    }
    return step(a, b)
}
