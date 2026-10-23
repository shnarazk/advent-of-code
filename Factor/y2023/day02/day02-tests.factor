USING: arrays assocs combinators hashtables kernel prettyprint sequences
  math math.parser splitting tools.test
  aoc.y2023.day02.private
;
IN: aoc.y2023.day02

! Factor -e='"aoc.y2023.day02," dup load test'

{ H{ { 2 "green" } } } [ { "2 green" } >hashmap ] unit-test
