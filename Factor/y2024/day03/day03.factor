USING: regexp ;
USING:
  arrays
  combinators
  io
  kernel
  math
  math.parser
  prettyprint
  regexp
  sequences
  splitting
  strings
  aoc.lib.parser
;
IN: aoc.y2024.day03

<PRIVATE

: part1/line ( line -- number )
  R/ mul\((\d+),(\d+)\)/
  all-matching-slices
  [ >string
    3 tail "(,)" split [ "" = ] reject [ string>number ] map
    product ] map
  sum
; inline

: part2/line ( line -- number )
  drop 2
; inline

: part1 ( data -- number ) [ part1/line ] map sum ;
: part2 ( data -- number ) [ part2/line ] map sum ;

PRIVATE>

: y2024day03 ( str -- )
  string>lines
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
