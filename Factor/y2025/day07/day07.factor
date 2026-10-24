USING:
  arrays assocs combinators hash-sets io kernel
  hash-sets hashtables math prettyprint sequences sets
  aoc.lib.parser
  aoc.lib.sequences
;
IN: aoc.y2025.day07

<PRIVATE

: part1/add-branch ( current-count pos -- current'-count' )
  [ [ first ] dip over adjoin ]
  [ drop second ]
  2bi
  2array
;

: part1/increment-count ( current-count -- current-count' )
  first2 1 + 2array
;

: part1/update-branches ( mapping positions-count -- positions'-count' )
  first2 [ members ] dip        ! ( mapping positions count )
  -rot { } >hash-set 0 2array   ! ( count mapping positions {}-0 )
  [                       ! ( mapping set-number position )
    pick                  ! ( mapping set-number position mapping )
    dupd in?              ! ( mapping set-number position ? )
    [
      [ 1 - ] [ 1 + ] bi  ! ( mapping set-number pos-1 pos+1 )
      swapd part1/add-branch    ! ( mapping pos-1 set'-number' )
      swap part1/add-branch     ! ( mapping set''-number'' )
      part1/increment-count
    ]
    [
      part1/add-branch         ! (mapping set'-number' )
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
    swap part1/update-branches
  ]
  reduce                 ! current-count
  second
;

: part2/add-branch ( hashtable pos count -- hashtable )
  [ swap 0 or + ] curry
  pick swap
  change-at
;

: part2/update-branches ( mapping hashtable -- hashtable )
  [ H{ } clone 2array ] dip  ! ( { mapping scratch } hashtable )
  [                      ! ( { mapping scratch } key value -- { mapping scratch } )
    pick first           ! ( { m s } key val mapping )
    pick swap in?        ! ( { m s } key val ? )
    [
      3dup                 ! ( { m s } key val { m s } key val )
      [ 1 - ] dip          ! ( { m s } key val { m s } key-1 val )
      [ second ] 2dip      ! ( { m s } key val s key-1 val )
      part2/add-branch     ! ( { m s } key val s' )
      -rot [ 1 + ] dip     ! ( { m s } s' key+1 val )
      part2/add-branch     ! ( { m s } s'' )
      [ first ] dip 2array
    ]
    [ [ first2 ] 2dip part2/add-branch 2array ]   ! ( m s key val )
    if
  ]
  assoc-each
  second
;


: part2 ( mappings start -- number )
  1 2array 1array >hashtable       ! (mappings hashtable )
  [ swap part2/update-branches ]   ! ( hashtable mapping )
  reduce                           ! hashtable
  values sum
;

PRIVATE>

: y2025day07 ( str -- )
  string>lines
  [ [ CHAR: . = ] unsatisfying-indices ] map [ length zero? ] reject
  [ 1 tail [ >hash-set ] map ] [ first first ] bi
  [ part1 ] [ part2 ] 2bi
  [ pprint "" print ] bi@
;
