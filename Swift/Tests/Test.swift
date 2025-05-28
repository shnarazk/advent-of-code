//
//  Test.swift
//  aoc
//

import Testing

@testable import Y2024

struct Y2024Tests {
    @Test("check within (y2024 day06)")
    func test_within() throws {
        #expect(Y2024.within((1, 1), in: (2, 2)) ?? (-1, -1) == (1, 1))
        #expect(Y2024.within((-1, 1), in: (2, 2)) == nil)
        #expect(Y2024.within((1, 8), in: (2, 2)) == nil)
    }

    @Test("check append_digits (y2024 day07)")
    func test1() throws {
        // Write your test here and use APIs like `#expect(...)` to check expected conditions.
        #expect(Y2024.append_digits(0, 12) == 12)
        #expect(Y2024.append_digits(10, 12) == 1012)
        #expect(Y2024.append_digits(120, 34) == 12034)
    }
}
