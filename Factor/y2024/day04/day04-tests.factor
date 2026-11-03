USING: kernel sequences tools.test
  aoc.y2024.day04.private
;
IN: aoc.y2024.day04

! Factor -e='"aoc.y2024.day04" dup load test'

{ { { 0 0 } { 1 -1 } { 2 -2 } { 3 -3 } } } [ { 1 -1 } { 0 0 } vector-length4 ] unit-test
{ { { 2 1 } { 3 0 } { 4 -1 } { 5 -2 } } } [ { 1 -1 } { 2 1 } vector-length4 ] unit-test
