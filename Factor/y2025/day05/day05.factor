USING: arrays ;
USING:
  accessors arrays assocs combinators io kernel
  math math.parser prettyprint sequences sorting splitting unicode
  aoc.lib.parser
;
IN: aoc.y2025.day05

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

: in-range? ( target range -- ? ) [ from>> >= ] [ to>> <= ] 2bi and ;

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
    [ from>> 0 2array ] [ to>> 1 2array ] bi
    rot
    swap prefix
    swap prefix
  ]
  reduce
  sort
;

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
