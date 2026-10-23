USING:
  arrays combinators io kernel math prettyprint sequences splitting unicode
  aoc.lib.parser
;
IN: aoc.y20YY.dayDD

<PRIVATE

: part1/line ( line -- number )
  drop 1
; inline

: part2/line ( line -- number )
  drop 2
; inline

: part1 ( data -- number ) [ part1/line ] map sum ;
: part2 ( data -- number ) [ part2/line ] map sum ;

PRIVATE>

: y20XXdayDD ( str -- )
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
