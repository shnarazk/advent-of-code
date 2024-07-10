#!/usr/bin/env Factor
! Copyright (C) 2024 Narazaki, Shuji.
! See https://factorcode.org/license.txt for BSD license.
USING: advent-of-code-2023 advent-of-code-2023.day01
arrays combinators formatting io kernel math math.parser prettyprint
sequences splitting unicode ;
IN: aoc

: run-aoc ( -- ) [ day01 ] benchmark 1000000.0 / pprint ;

MAIN: run-aoc
