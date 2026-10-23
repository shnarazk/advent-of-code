USING:
  accessors arrays combinators io kernel math math.parser prettyprint
  sequences splitting unicode
  aoc.lib.parser aoc.lib.sequences sets
;
IN: aoc.y2024.day02

<PRIVATE

: part1/line ( line -- number )
  window2
  [ [ first2 - abs [ 1 >= ] [ 3 <= ] bi and ] all? ]
  [ [ [ first2 < ] all? ] [ [ first2 > ] all? ] bi or ] bi and
; inline

: part1 ( data -- number ) [ part1/line ] filter length ;


: part2/line ( line -- ? )
 dup part1/line
 [ drop t ]
 [ dup length <iota> [ over remove-nth ] map nip [ part1/line ] any? ]
 if
; inline

: part2 ( data -- number ) [ part2/line ] filter length ;

PRIVATE>

: y2024day02 ( str -- )
  string>lines [ " " split [ string>number ] map ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
