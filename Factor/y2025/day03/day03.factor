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

! `seq` is from the most significant digit to the least significant digit
: seq>number ( seq -- number )
  0
  [ swap 10 * + ]
  reduce
; inline

{ 21 } [ { 2 1 } seq>number ] unit-test
{ 1203 } [ { 1 2 0 3 } seq>number ] unit-test

: number>seq ( number -- seq )
  dup zero?
  [ drop { } ]
  [ [ 10 /i number>seq ] [ 10 mod ] bi suffix ]
  if
; recursive

{ { 5 0 1 2 } } [ 5012 number>seq ] unit-test

: part1/line ( line -- value )
  reverse
  2 cut
  swap
  reverse
  [                    ! ( { t l } elt -- next )
    swap               ! ( elt { t l } )
    first2             ! ( elt t l )
    swap               ! ( elt l t )
    rot                ! ( l t elt )
    2dup <=             ! ( l t elt (t <= elt) )
    [ -rot max { } 2sequence ]
    [ drop swap { } 2sequence ]
    if
  ]
  reduce
  seq>number
; inline

: inject ( list digit -- new-list )
  over length zero?
  [ swap swap drop ]
  [ 2dup swap first >=
    [ swap 1 cut swap first inject swap prefix ]
    [ drop ]
    if
  ]
  if
; recursive

! { { } } [ { } 5 inject ] unit-test
! { { 5 } } [ { 1 } 5 inject ] unit-test
! { { 6 } } [ { 6 } 2 inject ] unit-test
! { { 5 3 1 } } [ { 3 0 1 } 5 inject ] unit-test

: part2/line ( line depth -- value )
  swap
  reverse
  swap cut
  swap
  reverse
  [ inject ] reduce
  seq>number
; inline

: part1 ( data -- number ) [ part1/line ] map sum ;
: part2 ( data -- number ) [ 12 part2/line ] map sum ;

PRIVATE>

: y2025day03 ( str -- )
  string>lines [ [ 48 - ] map { } like ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
