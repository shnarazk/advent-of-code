//
//  Test.swift
//  aoc
//

import Y2024
import Testing

struct Y2024Tests {

    @Test("check append_digits (y2024 day07)") func test1() throws {
        // Write your test here and use APIs like `#expect(...)` to check expected conditions.
        #expect(Y2024.append_digits(0, 12) == 12)
        #expect(Y2024.append_digits(10, 12) == 1012)
        #expect(Y2024.append_digits(120, 34) == 12034)
    }
}
