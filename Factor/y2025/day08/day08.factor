USING:
  arrays
  combinators
  io
  kernel
  math
  math.parser
  prettyprint
  sequences
  splitting
  unicode
  aoc.lib.parser
;
IN: aoc.y2025.day08

<PRIVATE

TUPLE: union-group
  { n number read-only }
  { new-group-id number }
  { group-layer }         ! group-id -> parent group-id
  { member }              ! node-id -> group-id
;

: union-group-new ( n -- union-group )
  0 { } pick f <array> union-group boa
;

GENERIC: group-id>> ( node-id class -- number )
GENERIC: >>group-id ( group-id node-id class -- )

M: union-group group-id>> member>> nth ;
M: union-group >>group-id member>> set-nth ;

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
