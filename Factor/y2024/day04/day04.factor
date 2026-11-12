USING:
  arrays combinators continuations io kernel
  math math.matrices math.vectors
  prettyprint sequences splitting aoc.lib.matrices
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

:: x-len3' ( base -- slash-and-backslash )
  { { -1 -1 } { 1  1 } } [ base v+ ] map
  { { -1  1 } { 1 -1 } } [ base v+ ] map
  2array
;

: ms/sm? ( 2chars matrix -- ? )
  '[ _ '[ _ matrix-nth ] [ 2drop f ] recover ] map
  [ { CHAR: M CHAR: S } = ] [ { CHAR: S CHAR: M } = ] bi or
;

:: part2 ( grid -- number )
    grid matrix-indices
    [ grid matrix-nth CHAR: A = ] filter
    [ x-len3' [ grid ms/sm? ] all? ] filter
    length
;

PRIVATE>

: y2024day04 ( str -- )
  string>lines [ >array ] map
  [ part1 ] [ part2 ] bi
  2array
;
