USING: kernel sequences tools.test
  aoc.y2024.day05.private
;
IN: aoc.y2024.day05

! Factor -e='"aoc.y2024.day05" dup load test'

{ 1 } [ 3 <iota> >array at-center ] unit-test
{ 4 } [ 9 <iota> >array at-center ] unit-test

{ H{ { 20 0 } { 30 1 } { 10 2 } } } [ { 20 30 10 } >nonble-table ] unit-test

{ { 1 3 } } [ { 3 1 3 1 1 } >uniq ] unit-test

{ { 3 4 } { 1 2 5 } } [ { 1 2 3 4 5 } { 3 4 8 } classify ] unit-test
