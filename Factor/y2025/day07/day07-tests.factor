USING: hash-sets kernel sequences tools.test
  aoc.y2025.day07.private
;
IN: aoc.y2025.day07

! Factor -e='"aoc.y2025.day07" dup load test'

{ { HS{ 2 8 4 } 5 } } [ { HS{ 2 8 } 5 } 4 part1/add-branch ] unit-test

{ { HS{ 2 8 4 } 6 } } [ { HS{ 2 8 } 5 }  part1/increment-count ] unit-test

{ { HS{ 5 } 1 } } [ HS{ 2 } { HS{ 5 } 1 } part1/update-branches ] unit-test

{ { HS{ 2 4 } 2 } } [ HS{ 3 } { HS{ 3 } 1 } part1/update-branches ] unit-test

{ H{ { 2 18 } } } [ H{ { 2 10 } } 2 8 part2/add-branch ] unit-test
