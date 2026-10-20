USING:
  arrays combinators io kernel math math.matrices prettyprint
  sequences splitting unicode
  aoclib.matrices aoclib.parser
;
IN: y2025.day04

<PRIVATE

: part1 ( matrix -- number )
  dup matrix-indices
  ...
  drop 1
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
