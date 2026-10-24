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
IN: aoc.y2025.day11

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

: y2025day11 ( str -- )
  string>lines [ ":" split first2 [ CHAR: \u000020 = ] trim " " split 2array ] map
  dup ...
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
