USING: kernel sequences tools.test
  aoc.y2025.day03.private
;
IN: aoc.y2025.day03

! Factor -e='"aoc.y2025.day03" dup load test'

{ 21 } [ { 2 1 } seq>number ] unit-test
{ 1203 } [ { 1 2 0 3 } seq>number ] unit-test

{ { 5 0 1 2 } } [ 5012 number>seq ] unit-test

{ { } } [ { } 5 inject ] unit-test
{ { 5 } } [ { 1 } 5 inject ] unit-test
{ { 6 } } [ { 6 } 2 inject ] unit-test
{ { 5 3 1 } } [ { 3 0 1 } 5 inject ] unit-test
