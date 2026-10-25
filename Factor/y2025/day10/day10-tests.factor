USING: kernel sequences tools.test
  aoc.y2025.day10.private
;
IN: aoc.y2025.day10

! Factor -e='"aoc.y2025.day10" dup load test'

! { } [ ] unit-test

{ { t f t } } [ "0-0" >array [ CHAR: 0 = ] map ] unit-test

{ { f t t f } } [ { f t f t } { f f t t } [ xor ] 2map ] unit-test

{ { f t t f } } [ { f t f t } { f f t t } apply-button ] unit-test
