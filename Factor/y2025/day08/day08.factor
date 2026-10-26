USING:
  arrays
  combinators
  io
  kernel
  math
  math.parser
  prettyprint
  sequences
  splitting
  unicode
  aoc.lib.parser
;
IN: aoc.y2025.day08

<PRIVATE

: iota-triangle ( n -- sequences )
  <iota> dup '[ _ swap 1 + tail ] map
;

: distance ( a b -- number ) [ - abs dup * ] 2map sum ; inline

: dist ( a b table -- number ) '[ _ at ] bi distance ; inline

: part1 ( table -- number ) drop 1 ;

: part2 ( table -- number ) drop 1 ;

PRIVATE>

: y2025day08 ( str -- )
  string>lines
  [ "," split [ string>number ] map ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
