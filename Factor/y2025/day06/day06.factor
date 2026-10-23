USING:
  arrays combinators io kernel math math.matrices math.parser
  prettyprint sequences splitting strings tools.test unicode
  aoc.lib.parser
;
IN: aoc.y2025.day06

<PRIVATE

: part1/line ( line -- number )
  drop 1
; inline

: part2/line ( line -- number )
  drop 2
; inline

: mul? ( char -- ? ) CHAR: * = ;

: part1 ( matrix -- number )
  dup length 1 - cut
  [ [ " " split [ "" = not ] filter [ string>number ] map ] map transpose ]
  [ first " " split [ "" = not ] filter [ first ] map ]
  bi*
  [ mul? [ product ] [ sum ] if ] 2map sum
;

: part2 ( matrix -- number )
  [
    transpose [ 1 head* >string [ CHAR: \u000020 = ] trim ] map
    [ string>number ] map { f } split
  ]
  [
    [ "  0123456789" split [ "" = not ] filter ] map {  } join [ first ] map
  ]
  bi
  [ mul? [ product ] [ sum ] if ] 2map sum
  ;

PRIVATE>

: y2025day06 ( str -- )
  string>lines
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
