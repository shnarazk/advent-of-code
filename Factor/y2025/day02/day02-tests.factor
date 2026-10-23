USING: kernel sequences sequences.repeating tools.test
  aoc.y2025.day02.private
;
IN: aoc.y2025.day02

! Factor -e='"aoc.y2025.day02" dup load test'

{ 2 4 f } [ 9 4 div-m? ] unit-test
{ 2 4 f } [ 9 4 div-m? ] unit-test

{ "11" } [ "12" 2 1 swapd head swap repeat ] unit-test

{ t } [ 110110 n-repeat? ] unit-test
{ f } [ 111110 n-repeat? ] unit-test
{ f } [ 110111 n-repeat? ] unit-test
