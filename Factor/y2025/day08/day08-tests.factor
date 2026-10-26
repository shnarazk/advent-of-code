USING: kernel sequences tools.test
  aoc.y2025.day08.private
;
IN: aoc.y2025.day08

! Factor -e='"aoc.y2025.day08" dup load test'

{ 1 4 9 } sum '{ _ } [ { 0 0 0 } { 1 2 3 } distance ] unit-test

{ { { 0 1 } { 0 2 } { 1 2 } } } [ 3 iota-triangle ] unit-test


{ f } [ 5 union-group-new 0 swap group-id>> ] unit-test

{ 10 }
[
  5 union-group-new 10 1 pick >>group-id
  1 swap group-id>>
] unit-test
