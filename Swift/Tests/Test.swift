//
//  Test.swift
//  aoc
//

import Y2024
import Testing

struct Y2024Tests {

    @Test func test1() async throws {
        // Write your test here and use APIs like `#expect(...)` to check expected conditions.
        #expect(Y2024.append_digits(10, 12) == 1012)
    }
}
