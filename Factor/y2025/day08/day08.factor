USING:
  accessors
  arrays
  combinators
  io
  kernel
  math
  math.parser
  multiline
  prettyprint
  sequences
  sorting
  splitting
  unicode
  aoc.lib.parser
;
IN: aoc.y2025.day08

<PRIVATE

TUPLE: union-group
  { n number read-only }  ! number of nodes
  { group array }         ! group-id -> parent group-id
  { membership array }    ! node-id -> group-id
;

: union-group-new ( n -- union-group )
  { } over f <array> union-group boa
;

GENERIC: new-group-id ( self -- group-id )
M: union-group new-group-id
  [ f suffix ] change-group group>> length 1 -
;

{ 1 } [ 1 union-group-new n>> ] unit-test
{ 0 } [ 2 union-group-new new-group-id ] unit-test

GENERIC: set-group-id ( group-id node-id class -- )
M: union-group set-group-id  membership>> set-nth ;

GENERIC: group-id ( node-id item -- number/f )
M:: union-group group-id ( node-id self -- group-id/id )
  node-id self membership>> nth
  dup
  [ [ self group>> nth dup f = not ] [ ] while ]
  [ ]
  if
;

! GENERIC: add-group ( class -- number )
! M:
! GENERIC: add-nodes ( node1 node2 class -- )
! GENERIC: merge-groups ( group1 group2 class -- )

! 4 union-group-new 1 2 pick group-id>> /* 0 over group-id>> */ ...

! M:: union-group add-nodes ( a b self -- )
!   ! TODO
! ;

{ t f } [ t 2 3 union-group-new group-id ] unit-test
{ t f } [ t 2 3 union-group-new dup new-group-id 2 pick set-group-id group-id ] unit-test

: iota-triangle ( n -- sequence )
  <iota> dup dup '[ _ swap 1 + tail ] map but-last
  [ swap '[ _ swap 2array ] map ] 2map
  { } join
;

: distance ( a b -- number ) [ - abs dup * ] 2map sum ; inline

: dist ( a b table -- number ) '[ _ nth ] 2over rot bi@ distance 3array ; inline

: part1 ( table -- number ) drop 1 ;

: part2 ( table -- number ) drop 1 ;

PRIVATE>

: y2025day08 ( str -- )
  string>lines
  [ "," split [ string>number ] map ] map
  dup length iota-triangle
  [ first2 pick dist ] map [ 2 swap nth ] sort-by [ but-last ] map
  drop
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
