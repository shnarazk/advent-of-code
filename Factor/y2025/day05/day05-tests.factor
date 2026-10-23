USING: accessors arrays kernel sequences tools.test
  aoc.y2025.day05.private
;
IN: aoc.y2025.day05

! Factor -e='"aoc.y2025.day05" dup load test'

{ 1 } [ "1-5" string>range from>> ] unit-test
{ 5 } [ "1-5" string>range to>> ] unit-test

{ t } [ 3 1 5 range-new in-range? ] unit-test
{ t } [ 5 1 5 range-new in-range? ] unit-test
{ f } [ 1 3 5 range-new in-range? ] unit-test
{ f } [ 8 1 5 range-new in-range? ] unit-test

{ { { 1 0 } { 2 1 } } } [ 1 2 range-new 1array >sorted ] unit-test
