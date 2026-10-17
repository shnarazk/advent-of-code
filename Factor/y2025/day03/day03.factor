USING:
  arrays combinators io kernel math math.order
  prettyprint sequences splitting unicode
  aoclib.parser
;
IN: y2025.day03

<PRIVATE

: sort2 ( obj1 obj2 -- smaller larger ) 2dup > [ swap ] when ;

! { 1 2 } [ 1 2 sort2 ] unit-test
! { 1 2 } [ 2 1 sort2 ] unit-test

: seq>number ( seq -- number )
  reverse
  0
  [ swap 10 * + ]
  reduce
; inline

! { 21 } [ { 1 2 } seq>number ] unit-test
! { 3021 } [ { 1 2 0 3 } seq>number ] unit-test

: part1/line ( line -- value )
  reverse
  2 cut
  swap
  [                    ! ( { l t } elt -- next )
    swap               ! ( elt { l t } )
    first2             ! ( elt l t )
    rot                ! ( l t elt )
    2dup <=             ! ( l t elt (t <= elt) )
    [ -rot max swap { } 2sequence ]
    [ drop { } 2sequence ]
    if
  ]
  reduce
  seq>number
; inline

! { } [  ] unit-test

: part2/line ( line -- number )
  reverse
  12 cut
  swap
  [                    ! ( { ... } elt -- next )
    drop
  ]
  reduce
  first2
  10 * +
; inline

: part1 ( data -- number ) [ part1/line ] map sum ;
: part2 ( data -- number ) [ part2/line ] map sum ;

PRIVATE>

: y2025day03 ( str -- )
  string>lines [ [ 48 - ] map { } like ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
