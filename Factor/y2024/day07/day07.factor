USING:
  arrays
  ! accessors
  combinators
  io
  kernel
  math
  math.parser
  prettyprint
  sequences
  splitting
  ! unicode
  aoc.lib.parser
;
IN: aoc.y2024.day07

<PRIVATE

: part1/line ( line -- number )
  ... 1
; inline

: part2/line ( line -- number )
  drop 2
; inline

: part1 ( data -- number ) [ part1/line ] map sum ;
: part2 ( data -- number ) [ part2/line ] map sum ;

PRIVATE>

: y2024day07 ( str -- )
  string>lines
  [ ":" split first2
    [ string>number ]
    [ " " split [ empty? ] reject [ string>number ] map ]
    bi*
    2array ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
