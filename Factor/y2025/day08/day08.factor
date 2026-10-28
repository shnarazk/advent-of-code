USING: kernel ;
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

: union-group-new ( n -- union-group ) { } over f <array> union-group boa ;

GENERIC: new-group-id ( self -- group-id )
M: union-group new-group-id [ f suffix ] change-group group>> length 1 - ;

GENERIC: add-to-new-group ( node-id self -- )
M:: union-group add-to-new-group ( node-id self -- )
  self [ f suffix ] change-group group>> length 1 -
  node-id self membership>> set-nth
;

GENERIC: set-group ( group-id node-id self -- )
M: union-group set-group membership>> set-nth ;

GENERIC: set-parent-group ( parent-group-id group-id self -- )
M:: union-group set-parent-group ( parent-group-id group-id self -- )
  parent-group-id group-id =
  [
    parent-group-id f = [ "eee2" ... 2 exit ] when
    group-id f = [ "eee3" ... 2 exit ] when
    parent-group-id group-id self group>> set-nth
  ] unless
;

GENERIC: group-id ( node-id self -- group-id/f )
M:: union-group group-id ( node-id self -- group-id/d )
  node-id self membership>> nth
  dup
  [ dup [ self group>> nth dup f = not ] [ nip dup ] while drop ]
  when
;

GENERIC: merge-groups ( from-group into-group self -- )
M: union-group merge-groups ( from into self -- ) swapd set-parent-group ;

GENERIC: dispatch ( node-pair self -- )
M:: union-group dispatch ( node-pair self -- )
  node-pair dup [ self group-id ] map
  dup [ not not ] map
  { { { f f } [ drop self new-group-id '[ _ swap self set-group ] each ] } !
    { { f t } [ [ first ] [ second ] bi* swap self set-group ] }
    { { t f } [ [ second ] [ first ] bi* swap self set-group ] }
    { { t t } [ first2 self merge-groups drop ] } }
  case
;

: iota-triangle ( n -- sequence )
  <iota> dup dup '[ _ swap 1 + tail ] map but-last
  [ swap '[ _ swap 2array ] map ] 2map
  { } join
;

: distance ( a b -- number ) [ - abs dup * ] 2map sum ; ! inline

: dist ( a b table -- number ) '[ _ nth ] 2over rot bi@ distance 3array ; ! inline

: part1 ( table order -- number )
  over length union-group-new
  swap over '[ _ dispatch ] each
  ...
  drop 1 ;

: part2 ( table order -- number ) 2drop 1 ;

PRIVATE>

: y2025day08 ( str -- )
  string>lines
  [ "," split [ string>number ] map ] map
  dup length iota-triangle
  [ first2 pick dist ] map [ 2 swap nth ] sort-by [ but-last ] map
  [ part1 ] [ part2 ] 2bi
  [ pprint "" print ] bi@
;
