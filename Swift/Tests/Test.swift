//
//  Test.swift
//  aoc
//

import Testing

@testable import Utils
@testable import Y2024

struct UtilsTests {

    @Test("Check Pos (Utils geometory")
    func test_pos() throws {
        #expect(Pos(y: 1, x: 1).within(Pos(y: 2, x: 2))! == Pos(y: 1, x: 1))
        #expect(Pos(y: 1, x: -1) + Pos(y: 2, x: 5) == Pos(y: 3, x: 4))
    }

    @Test("check within function (Utils geometory)")
    func test_within() throws {
        #expect(within((1, 1), in: (2, 2)) ?? (-1, -1) == (1, 1))
        #expect(within((-1, 1), in: (2, 2)) == nil)
        #expect(within((1, 8), in: (2, 2)) == nil)
    }
}

struct Y2024Tests {

    @Test("check append_digits (y2024 day07)")
    func test1() throws {
        // Write your test here and use APIs like `#expect(...)` to check expected conditions.
        #expect(Y2024.append_digits(0, 12) == 12)
        #expect(Y2024.append_digits(10, 12) == 1012)
        #expect(Y2024.append_digits(120, 34) == 12034)
    }
}
