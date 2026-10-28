USING: kernel sequences tools.test
  aoc.y2025.day08.private
;
IN: aoc.y2025.day08

! Factor -e='"aoc.y2025.day08" dup load test'

{ 1 } [ 1 union-group-new n>> ] unit-test
{ 0 } [ 2 union-group-new new-group-id ] unit-test

{ { f f f } } [ 3 union-group-new membership>> ] unit-test

{ { f 0 f } } [ 3 union-group-new 1 over add-to-new-group membership>> ] unit-test

{ { 1 0 f } }
[ 3 union-group-new
  1 over add-to-new-group
  0 over add-to-new-group
  membership>> ]
unit-test

{ { 2 0 f } }
[ 3 union-group-new
  0 over add-to-new-group
  1 over add-to-new-group
  2 over add-to-new-group
  0 1 pick set-parent-group
  2 0 pick set-parent-group
  group>>
] unit-test

{ f } [ 4 union-group-new 0 over add-to-new-group 1 swap group-id ] unit-test
{ 0 } [ 4 union-group-new 1 over add-to-new-group 1 swap group-id ] unit-test

{ { 1 2 f } }
[ 3 union-group-new
  0 over add-to-new-group
  1 over add-to-new-group
  2 over add-to-new-group
  0 1 pick merge-groups
  1 2 pick merge-groups
  group>>
] unit-test

{ { 2 2 2 } }
[ 3 union-group-new
  0 over add-to-new-group
  1 over add-to-new-group
  2 over add-to-new-group
  0 1 pick merge-groups
  1 2 pick merge-groups
  { 0 1 2 } [ over group-id ] map
  nip
] unit-test

{ { 0 0 1 1 0 } }
[ 5 union-group-new
  { 0 1 } over dispatch
  { 1 4 } over dispatch
  { 2 3 } over dispatch
  5 <iota> [ over group-id ] map
  nip
] unit-test

{ 1 4 9 } sum '{ _ } [ { 0 0 0 } { 1 2 3 } distance ] unit-test

{ { { 0 1 } { 0 2 } { 1 2 } } } [ 3 iota-triangle ] unit-test
