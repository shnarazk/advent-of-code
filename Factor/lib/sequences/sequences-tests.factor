USING: kernel math sequences tools.test
  ! aoc.lib.sequences.private
;
IN: aoc.lib.sequences

! Factor -e='"aoc.lib.sequences" dup load test'

{ { { 1 2 } { 2 3 } { 3 4 } } } [ { 1 2 3 4 } window2 ] unit-test

{ { 2 3 } } [ { 1 2 0 0 2 } [ zero? ] satisfying-indices ] unit-test

{ { 0 2 } } [ { 1 2 3 2 2 } [ 2 = ] !satisfies ] unit-test
{ { 0 2 4 } } [ { 1 0 3 0 2 } [ zero? ] !satisfies ] unit-test
