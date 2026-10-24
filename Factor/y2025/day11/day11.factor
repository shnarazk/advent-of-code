USING:
  arrays assocs combinators hashtables io kernel math
  prettyprint sequences splitting unicode
  aoc.lib.parser
;
IN: aoc.y2025.day11

<PRIVATE

: part1/pathes ( hashtable from -- number )
  dup "out" =
  [ 2drop 1 ]
  [ over at* ! ( hashtable adjacents/f ? )
    [ [ dupd part1/pathes ] map sum nip ]
    [ 2drop 0 ]
    if ]
  if
;

: part1 ( hashtable -- number ) "you" part1/pathes ;

MEMO: part2/pathes ( hashtable from to -- number )
  2dup =
  [ 3drop 1 ]
  [ -rot over at* ! ( to hashtable adjacents/f ? )
    [ [ 2over -rot part2/pathes ] map sum 2nip ]
    [ 3drop 0 ]
    if ]
  if
;

: part2 ( hashtable -- number )
  [ [ "svr" "dac" part2/pathes ]
    [ "dac" "fft" part2/pathes ]
    [ "fft" "out" part2/pathes ]
    tri * * ]
  [ [ "svr" "fft" part2/pathes ]
    [ "fft" "dac" part2/pathes ]
    [ "dac" "out" part2/pathes ]
    tri * * ]
  bi
  +
;

PRIVATE>

: y2025day11 ( str -- )
  string>lines
  [ ":" split first2 [ CHAR: \u000020 = ] trim " " split 2array ] map
  >hashtable
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
