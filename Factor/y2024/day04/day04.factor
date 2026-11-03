USING: math.matrices ;
USING:
  arrays
  ! accessors
  combinators
  io
  kernel
  math
  math.vectors
  prettyprint
  sequences
  splitting
  ! unicode
  aoc.lib.parser
;
IN: aoc.y2024.day04

<PRIVATE

:: vector-length4 ( dir base -- 4seq )
  4 <iota> [ dir swap v*n base v+ ] map
;

:: part1 ( grid -- number )
  [let
    grid dimension first :> height
    grid dimension second :> width
    height width +
  ]
;

: part2 ( grid -- number ) drop 1 ;

PRIVATE>

: y2024day04 ( str -- )
  string>lines [ >array ] map
  dup ...
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
