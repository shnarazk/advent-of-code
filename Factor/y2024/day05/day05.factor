USING: assocs ;
USING:
  accessors
  arrays
  assocs
  combinators
  io
  kernel
  math
  math.parser
  prettyprint
  sequences
  splitting
  strings
  ! unicode
  aoc.lib.parser
;
IN: aoc.y2024.day05

<PRIVATE

: at-center ( sequence -- number )
  dup length 2 /i swap nth
;

: >nonble-table ( sequence -- hashtable )
  H{ } clone swap
  dup [ length <iota> ] dip
  [ pick set-at ] 2each
;

: part1/find ( pages constraints -- number )
  [ [ at-center ] [ >nonble-table ] bi ] dip
  swap
  '[ _ swap [ over at ] map
    dup [ not not ] map
    {
      { { f f } [ drop t ] }
      { { f t } [ drop t ] }
      { { t f } [ drop t ] }
      [ drop first2 < ]
    }
    case
    nip
  ]
  all?
  [ drop 0 ] unless
; inline

: part2/find ( pages constraints -- number ) 2drop 2 ; inline

: part1 ( orderings targets -- number ) swap '[ _ part1/find ] map sum ;
: part2 ( orderings targets -- number ) swap '[ _ part2/find ] map sum ;

PRIVATE>

: y2024day05 ( str -- )
  "\n\n" split-subseq [ >string ] map first2 [ "\n" split ] bi@
  [ [ "|" split [ string>number ] map ] map ]
  [ [ empty? ] reject [ "," split [ string>number ] map ] map ]
  bi*
  [ part1 ] [ part2 ] 2bi
  [ pprint "" print ] bi@
;
