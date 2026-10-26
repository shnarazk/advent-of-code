USING: kernel sequences tools.test
  aoc.y2025.day08.private
;
IN: aoc.y2025.day08

! Factor -e='"aoc.y2025.day08" dup load test'

{ 1 4 9 } sum '{ _ } [ { 0 0 0 } { 1 2 3 } distance ] unit-test

{ { { 1 2 } { 2 } { } } } [ 3 iota-triangle ] unit-test
