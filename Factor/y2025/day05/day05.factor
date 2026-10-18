USING:
  accessors arrays combinators io kernel math math.parser prettyprint
  sequences splitting unicode
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

: part2 ( ranges _ -- number )
  drop length
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
