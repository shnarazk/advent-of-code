USING: sequences ;
USING:
  arrays combinators io kernel math math.parser prettyprint
  sequences splitting unicode
  aoclib.parser
;
IN: y2025.day02

<PRIVATE

: 2repeat? ( number -- ? )
  number>string
  dup length 2 /i cut
  =
;

: part1/loop ( limit n -- number )
  2dup >=
  [ dup 2repeat? [ dup -rot 1 + part1/loop + ] [ 1 + part1/loop ] if ]
  [ 2drop 0 ]
  if
; recursive

: part1/line ( beg-end -- number ) first2 swap part1/loop ; inline

: part2/line ( number -- number )
  ! >string
  drop 2
; inline

: part1 ( data -- number ) [ part1/line ] map sum ;
: part2 ( data -- number ) [ part2/line ] map sum ;

PRIVATE>

: y2025day02 ( str -- )
  "," split [ [ CHAR: \n = ] trim "-" split [ string>number ] map ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
