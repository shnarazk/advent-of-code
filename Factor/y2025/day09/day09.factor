USING:
  arrays
  combinators
  io kernel
  math
  prettyprint
  sequences
  splitting
  unicode
  aoc.lib.parser
;
IN: aoc.y2025.day09

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

: y2025day09 ( str -- )
  string>lines [ "," split [ string>number ] map ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
