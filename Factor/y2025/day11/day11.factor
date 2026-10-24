USING: hashtables assocs xml.data ;
USING:
  arrays
  combinators
  hashtables
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

: pathes ( hashtable from -- number )
  dup "out" =
  [ 2drop 1 ]
  [ over at* ! ( hashtable adjacents/f ? )
    [ [ dupd pathes ] map sum nip ]
    [ 2drop 0 ]
    if ]
  if
;

: part1 ( hashtable -- number ) "you" pathes ;

: part2 ( hashtable -- number ) drop 1 ;

PRIVATE>

: y2025day11 ( str -- )
  string>lines
  [ ":" split first2 [ CHAR: \u000020 = ] trim " " split 2array ] map
  >hashtable
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
