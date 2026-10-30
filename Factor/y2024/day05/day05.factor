USING:
  accessors arrays assocs combinators combinators.short-circuit io
  kernel math math.parser prettyprint sequences sets splitting strings
  aoc.lib.parser
;
IN: aoc.y2024.day05

<PRIVATE

: at-center ( sequence -- number )
  dup length 2 /i swap nth
; inline

: >nonble-table ( sequence -- hashtable )
  H{ } clone swap
  dup [ length <iota> ] dip
  [ pick set-at ] 2each
; inline

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

: >uniq ( sequence -- sequence )
  HS{ } clone swap
  [ over adjoin ] each
  members
; inline

: classify ( target criterion -- includes excludes )
  '[ _
    [ dup ] dip member?
    [ [ [ first ] dip suffix ] [ drop second ] 2bi 2array ]
    [ [ drop first ] [ [ second ] dip suffix ] 2bi 2array ]
    if ]
  { { } { } }
  swap reduce
  first2
; inline

: part2/find ( pages constraints -- number )
  [ [ over member? ] map { t t } = ] filter        ! ( pages constraints' )
  { } -rot                                 ! ( scratch pages constraints' )
  [ dup empty? not ]
  [  dup [ second ] map >uniq    ! ( scratch pages constraints' backseats )
    pick swap classify   ! ( scratch pages constraints' includes excludes )
    dup length 1 assert=
    nip first                    ! ( scratch pages constrains top )
    [ '[ 2drop _ suffix ] ]
    [ '[ drop nip _ swap remove ] ]
    [ '[ 2nip _ '[ first _ = ] reject ] ]
    tri
    3tri ]
  while
  drop
  append
  at-center
;

: part1 ( orderings targets -- number ) swap '[ _ part1/find ] map sum ;
: part2 ( orderings targets -- number )
  over '[ _ part1/find zero? ] filter
  swap '[ _ part2/find ] map sum
;

PRIVATE>

: y2024day05 ( str -- )
  "\n\n" split-subseq [ >string ] map first2 [ "\n" split ] bi@
  [ [ "|" split [ string>number ] map ] map ]
  [ [ empty? ] reject [ "," split [ string>number ] map ] map ]
  bi*
  [ part1 ] [ part2 ] 2bi
  [ pprint "" print ] bi@
;
