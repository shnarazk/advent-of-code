USING: arrays assocs combinators hashtables kernel prettyprint sequences
  math math.parser splitting tools.test
  aoc.y2023.day02.private
;
IN: aoc.y2023.day02

! Factor -e='"aoc.y2023.day02," dup load test'

{ H{ { "green" 2 } } } [ { "2 green" } >hashmap ] unit-test

{ 39 } [ 0 mybag [ nip + ] assoc-each ] unit-test

{ { "k" 1 } } [ H{ { "k" 1 } } "k" key-num ] unit-test

{ H{ { "blue" 14 } { "green" 13 } { "red" 12 } } } [ mybag { "blue" "red" } >key-vals ] unit-test

{ mybag } [ mybag mybag union-bags ] unit-test
