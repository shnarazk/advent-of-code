//
//  Test.swift
//  aoc
//

import Testing

@testable import Utils
@testable import Y2024

struct UtilsTests {

    @Test("Pos calculation (Utils geometory)")
    func test_pos() throws {
        #expect(Pos.zero + Pos.zero == Pos(y: 0, x: 0))
        #expect(Pos(y: 1, x: -1) + Pos(y: 2, x: 5) == Pos(y: 3, x: 4))
        #expect(Pos(y: 1, x: -1) - Pos(y: 2, x: 5) == Pos(y: -1, x: -6))
    }

    @Test("Pos boundary (Utils geometory)")
    func test_pos_boundary() throws {
        #expect(Pos(y: 1, x: 1).within(Pos(y: 2, x: 2))! == Pos(y: 1, x: 1))
        #expect(Pos(y: 2, x: 2).within(Pos(y: 2, x: 2))! == Pos(y: 2, x: 2))
        #expect(Pos(y: 2, x: 2).within(y: 3, x: 3)! == Pos(y: 2, x: 2))
        #expect(Pos(y: 2, x: 2).within(y: 2, x: 2) == nil)
        #expect(Pos(y: 1, x: 2).within(y: 2, x: 2) == nil)
    }

    @Test("Pos iteration (Utils geometory)")
    func test_pos_next() throws {
        #expect(Pos(y: 1, x: 1).next(upto: Pos(y: 2, x: 5)) == Pos(y: 1, x: 2))
        #expect(Pos(y: 1, x: 3).next(upto: Pos(y: 4, x: 3)) == Pos(y: 2, x: 0))
        #expect(Pos(y: 4, x: 3).next(upto: Pos(y: 4, x: 3)) == nil)
    }

    @Test("Pos neighbors (Utils geometory)")
    func test_pos_neighbors() throws {
        #expect(
            Pos(y: 1, x: 1).neighbors4(bound: Pos(y: 2, x: 5)) ==
            [Pos(y: 0, x: 1), Pos(y: 1, x: 2), Pos(y: 2, x: 1), Pos(y: 1, x: 0)]
        )
        #expect(
            Pos(y: 2, x: 2).neighbors4(bound: Pos(y: 3, x: 2)) ==
            [Pos(y: 1, x: 2), Pos(y: 3, x: 2), Pos(y: 2, x: 1)]
        )
        #expect(
            Pos(y: 2, x: 2).neighbors4(bound: Pos(y: 2, x: 2)) ==
            [Pos(y: 1, x: 2), Pos(y: 2, x: 1)]
        )
    }
    @Test("Pos 4 dirs (Utils geometory)")
    func test_pos_dirs() throws {
        #expect(Pos.north + Pos.south == Pos.zero)
        #expect(Pos.east + Pos.west == Pos.zero)
        #expect(Pos.north.turn_right() == Pos.east)
        #expect(Pos.east.turn_right() == Pos.south)
        #expect(Pos.south.turn_right() == Pos.west)
        #expect(Pos.west.turn_right() == Pos.north)
    }

    @Test("within function (Utils geometory)")
    func test_within() throws {
        #expect(within((1, 1), in: (2, 2)) ?? (-1, -1) == (1, 1))
        #expect(within((-1, 1), in: (2, 2)) == nil)
        #expect(within((1, 8), in: (2, 2)) == nil)
    }
}

struct Y2024Tests {

    @Test("append_digits function (y2024 day07)")
    func test1() throws {
        // Write your test here and use APIs like `#expect(...)` to check expected conditions.
        #expect(Y2024.append_digits(0, 12) == 12)
        #expect(Y2024.append_digits(10, 12) == 1012)
        #expect(Y2024.append_digits(120, 34) == 12034)
    }
}
