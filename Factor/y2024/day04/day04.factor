USING: math.matrices ;
USING:
  arrays
  ! accessors
  combinators
  continuations
  io
  kernel
  math
  math.vectors
  prettyprint
  sequences
  splitting
  aoc.lib.matrices
  aoc.lib.parser
;
IN: aoc.y2024.day04

<PRIVATE

:: vector-length4 ( dir base -- 4seq )
  4 <iota> [ dir swap v*n base v+ ] map
;

: xmas? ( index-arrow matrix -- ? )
  '[ _ '[ _ matrix-nth ] [ 2drop f ] recover ] map
  "XMAS" >array =
; inline

:: part1 ( grid -- number )
  [let
    grid matrix-indices :> indices
    indices [ {  0 -1 } swap vector-length4 grid xmas? ] filter length
    indices [ {  0  1 } swap vector-length4 grid xmas? ] filter length +
    indices [ { -1  0 } swap vector-length4 grid xmas? ] filter length +
    indices [ {  1  0 } swap vector-length4 grid xmas? ] filter length +
    indices [ { -1 -1 } swap vector-length4 grid xmas? ] filter length +
    indices [ {  1  1 } swap vector-length4 grid xmas? ] filter length +
    indices [ {  1 -1 } swap vector-length4 grid xmas? ] filter length +
    indices [ { -1  1 } swap vector-length4 grid xmas? ] filter length +
  ]
;

: part2 ( grid -- number ) drop 1 ;

PRIVATE>

: y2024day04 ( str -- )
  string>lines [ >array ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
