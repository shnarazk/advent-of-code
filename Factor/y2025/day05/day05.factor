USING:
  accessors arrays assocs combinators io kernel
  math math.parser prettyprint sequences sorting splitting unicode
  aoclib.parser
;
IN: y2025.day05

<PRIVATE

TUPLE: range from to ;

: range-new ( from to -- range )
  range new
  swap >>to
  swap >>from
;

: string>range ( string -- range )
  "-" split [ string>number ] map
  first2 range boa
 ;

! { 1 } [ "1-5" string>range from>> ] unit-test
! { 5 } [ "1-5" string>range to>> ] unit-test

: in-range? ( target range -- ? ) [ from>> >= ] [ to>> <= ] 2bi and ;

! { t } [ 3 1 5 range-new in-range? ] unit-test
! { t } [ 5 1 5 range-new in-range? ] unit-test
! { f } [ 1 3 5 range-new in-range? ] unit-test
! { f } [ 8 1 5 range-new in-range? ] unit-test

: part1/line ( target ranges -- 0/1 )
  [ dupd in-range? ] any? [ 1 ] [ 0 ] if nip
; inline

: part2/line ( line -- number )
  drop 2
; inline

: part1 ( ranges targets -- number ) [ over part1/line ] map sum nip ;

: >sorted ( ranges -- seq )
  { }
  [ ! ( set range )
    [ from>> 0 { } 2sequence ] [ to>> 1 { } 2sequence ] bi
    rot
    swap prefix
    swap prefix
  ]
  reduce
  sort
;

! { { { 1 1 } { 2 0 } } } [ 1 2 range-new { } 1sequence >set ] unit-test

: part2 ( ranges _ -- number )
  drop
  >sorted
  { 0 0 0 } ! { start count level }
  [
    first2 zero?           ! ( state pos )
    [ swap first3          ! ( pos start count level )
      dup zero?
      [ drop -rot          ! ( count pos start )
        drop swap 1        ! ( pos count 1 )
        { } 3sequence ]
      [ 1 + { } 3sequence nip ]
      if ]
    [ swap first3          ! ( pos start count level )
      1 - dup zero?        ! ( pos start count level' )
      [ drop swap -        ! ( pos count-start )
        over + 1 + 0       ! ( pos count' 0 )
        { } 3sequence ]
      [ { } 3sequence nip ]
      if ]
    if
  ]
  reduce
  second
;

PRIVATE>

: y2025day05 ( str -- )
  "\n\n" split1
  [ string>lines [ string>range ] map ]
  [ string>lines [ string>number ] map ]
  bi*
  [ part1 ] [ part2 ] 2bi
  [ pprint "" print ] bi@
;
