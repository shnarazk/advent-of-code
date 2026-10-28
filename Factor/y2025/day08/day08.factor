USING: kernel ;
USING:
  accessors arrays assocs combinators hashtables io kernel math math.parser
  multiline prettyprint sequences sorting splitting unicode
  aoc.lib.parser
;
IN: aoc.y2025.day08

<PRIVATE

TUPLE: union-group
  { group array }         ! group-id -> parent group-id
  { membership array }    ! node-id -> group-id
;

: union-group-new ( n -- union-group ) { } swap f <array> union-group boa ;

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
M: union-group set-parent-group ( parent-group-id group-id self -- )
  2over = [ 3drop ] [ group>> set-nth ] if
;

GENERIC: group-id ( node-id self -- group-id/f )
M:: union-group group-id ( node-id self -- group-id/d )
  node-id self membership>> nth
  dup
  [ dup [ self group>> nth dup f = not ] [ nip dup ] while drop ]
  when
; inline

GENERIC: merge-groups ( from-group into-group self -- )
M: union-group merge-groups ( from into self -- ) swapd set-parent-group ;

GENERIC: dispatch ( node-pair self -- )
M:: union-group dispatch ( node-pair self -- )
  node-pair dup [ self group-id ] map
  dup [ not not ] map
  { { { f f } [ drop self new-group-id '[ _ swap self set-group ] each ] } !
    { { f t } [ [ first ] [ second ] bi* swap self set-group ] }
    { { t f } [ [ second ] [ first ] bi* swap self set-group ] }
    { { t t } [ inv-sort first2 self merge-groups drop ] } }
  case
;

GENERIC: group-sizes ( self -- sequence )
M: union-group group-sizes ( self -- sequence )
  [ membership>> length <iota> ] [ '[ _ group-id ] ] bi map
  [ ] filter
  H{ } swap over '[ _ inc-at ] each
  values
  inv-sort
;

GENERIC: united? ( self -- ? )
M: union-group united?
  dup membership>> [ f = not ] all?
  [
    [ ] [ membership>> length <iota> ] [ 0 swap group-id ] tri
    '[ over group-id _ = ] all?
    nip
  ]
  [ drop f ]
  if
;

: iota-triangle ( n -- sequence )
  <iota> dup dup '[ _ swap 1 + tail ] map but-last
  [ swap '[ _ swap 2array ] map ] 2map
  { } join
;

: distance ( a b -- number ) [ - abs dup * ] 2map sum ; ! inline

: dist ( a b table -- number ) '[ _ nth ] 2over rot bi@ distance 3array ; ! inline

: part1 ( table order -- number )
  [ length ] dip
  over 20 = 10 1000 ? head
  [ union-group-new ] dip
  over '[ _ dispatch ] each
  group-sizes 3 head product
;

: part2 ( table order -- number )
  [ dup length union-group-new ] dip   ! ( table union-group order )
  f
  [ over f =
    [ nip 2dup swap dispatch over united? [ ] [ drop f ] if ]
    [ drop ]
    if ]
  reduce
  nip
  [ over nth first ] map product
  nip
;

PRIVATE>

: y2025day08 ( str -- )
  string>lines
  [ "," split [ string>number ] map ] map
  dup length iota-triangle
  [ first2 pick dist ] map [ 2 swap nth ] sort-by [ but-last ] map
  [ part1 ] [ part2 ] 2bi
  [ pprint "" print ] bi@
;
