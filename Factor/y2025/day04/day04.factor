USING:
  arrays combinators io kernel math math.matrices prettyprint
  sequences splitting unicode
  aoclib.matrices aoclib.parser
;
IN: y2025.day04

<PRIVATE

: part1 ( matrix -- number )
  dup 8neighbors-values
  [ 0 [ [ 1 ] [ 0 ] if + ] reduce 4 < [ 1 ] [ 0 ] if ] matrix-map
  swap [ [ 1 ] [ 0 ] if ] matrix-map
  m*
  [ sum ] map sum
;

: part2 ( matrix -- number )
  drop 1
;

PRIVATE>

: y2025day04 ( str -- )
  string>lines [ { } like [ CHAR: @ = ] map ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
