USING:
  arrays combinators io kernel math math.combinators math.parser
  prettyprint sequences splitting unicode
  aoclib.parser
;
IN: y2025.day01

<PRIVATE

: parse-line ( line -- number )
  1 cut
  string>number
  swap
  "L" =
  [ -1 * ] when
; inline

: part1/step ( count-pos turn -- next )
  swap [ first ] [ second ] bi rot ! ( count pos turn )
  + 100 mod
  [ 100 + ] [ ] if-negative
  dup zero? [ drop 1 + 0 ] [ ] if
  { } 2sequence
 ;

: part2/passing_mod100 ( now next -- inc next' )
  [
    [ 100 mod 100 + 100 mod ] [ abs 100 /i ] bi ! ( now next' inc )
    rot                                         ! ( next' inc now )
    zero? not [ 1 + ] when                      ! ( next' inc' )
    swap                                        ! ( inc' next' )
  ]
  [
    swap drop                                          ! ( next )
    [ dup zero? [ 1 + ] [ 100 /i ] if ] [ 100 mod ] bi ! ( inc next' )
  ]
  if-negative
 ; inline

! { 0  5 } [ 1    5 part2/passing_mod100 ] unit-test
! { 1  2 } [ 1  102 part2/passing_mod100 ] unit-test
! { 4  3 } [ 1  403 part2/passing_mod100 ] unit-test
! { 1  0 } [ 1    0 part2/passing_mod100 ] unit-test
! { 2 95 } [ 1 -105 part2/passing_mod100 ] unit-test
! { 1 98 } [ 0 -102 part2/passing_mod100 ] unit-test
! { 5 90 } [ 5 -410 part2/passing_mod100 ] unit-test

: part2/step ( count-pos turn -- next )
  swap [ first ] [ second ] bi ! ( turn count pos )
  rot                          ! ( count pos turn )
  dupd +                       ! ( count pos next )
  part2/passing_mod100         ! ( count inc next' )
  -rot +                       ! ( next' count' )
  swap { } 2sequence
 ; inline

: part1 ( turns -- number ) { 0 50 } [ part1/step ] reduce first ;
: part2 ( turns -- number ) { 0 50 } [ part2/step ] reduce first ;

PRIVATE>

: y2025day01 ( string -- )
  string>lines [ parse-line ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
