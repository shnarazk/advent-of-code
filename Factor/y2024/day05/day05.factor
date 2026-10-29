USING: splitting sequences ;
USING:
  arrays
  ! accessors
  combinators
  io
  kernel
  math
  ! math.parser
  prettyprint
  sequences
  splitting
  ! unicode
  aoc.lib.parser
;
IN: aoc.y2024.day05

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

: y2024day05 ( str -- )
  "\n\n" split-subseq [ >string ] map first2 [ "\n" split ] bi@
  [ [ "|" split [ string>number ] map ] map ]
  [ [ empty? ] reject [ "," split [ string>number ] map ] map ]
  bi*
  ...
  dup ...
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
