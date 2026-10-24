USING: kernel hash-sets ;
USING:
  arrays
  combinators
  hash-sets
  io kernel
  math
  prettyprint
  sequences
  ! splitting
  sets
  ! unicode
  aoc.lib.parser
  aoc.lib.sequences
;
IN: aoc.y2025.day07

<PRIVATE

: part2/line ( line -- number )
  drop 2
; inline

: add-branch ( current-count pos -- current'-count' )
  [ [ first ] dip over adjoin ]
  [ drop second ]
  2bi
  2array
;

: increment-count ( current-count -- current-count' )
  first2 1 + 2array
;

: update-branches ( mapping positions-count -- positions'-count' )
  first2 [ members ] dip        ! ( mapping positions count )
  -rot { } >hash-set 0 2array   ! ( count mapping positions {}-0 )
  [                       ! ( mapping set-number position )
    pick                  ! ( mapping set-number position mapping )
    dupd in?              ! ( mapping set-number position ? )
    [
      [ 1 - ] [ 1 + ] bi  ! ( mapping set-number pos-1 pos+1 )
      swapd add-branch    ! ( mapping pos-1 set'-number' )
      swap add-branch     ! ( mapping set''-number'' )
      increment-count
    ]
    [
      add-branch         ! (mapping set'-number' )
    ]
    if
  ]
  reduce                        ! ( count mapping positions'-count' )
  nip first2 rot                ! ( positions' count' count )
  + 2array
;

: part1 ( mappings start -- number )
  1array >hash-set 0 2array   ! (mappings current-0 )
  [                     ! ( current-count mapping )
    swap update-branches
  ]
  reduce                 ! current-count
  second
;
: part2 ( mapping start -- number ) drop [ part2/line ] map sum ;

PRIVATE>

: y2025day07 ( str -- )
  string>lines
  [ [ CHAR: . = ] unsatisfying-indices ] map [ length zero? ] reject
  [ [ >hash-set ] map ] [ first first ] bi
  [ part1 ] [ part2 ] 2bi
  [ pprint "" print ] bi@
;
