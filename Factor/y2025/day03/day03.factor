USING:
  arrays combinators io kernel math math.order
  prettyprint sequences splitting unicode
  aoc.lib.parser
;
IN: aoc.y2025.day03

<PRIVATE

! `seq` is from the most significant digit to the least significant digit
: seq>number ( seq -- number )
  0
  [ swap 10 * + ]
  reduce
; inline

: number>seq ( number -- seq )
  dup zero?
  [ drop { } ]
  [ [ 10 /i number>seq ] [ 10 mod ] bi suffix ]
  if
; recursive

: inject ( list digit -- new-list )
  over length zero?
  [ swap swap drop ]
  [ 2dup swap first >=
    [ swap 1 cut swap first inject swap prefix ]
    [ drop ]
    if
  ]
  if
; recursive

: maximize ( line depth -- value )
  [ reverse ] dip
  cut
  swap
  reverse
  [ inject ] reduce
  seq>number
; inline

: part1 ( data -- number ) [ 2 maximize ] map sum ;
: part2 ( data -- number ) [ 12 maximize ] map sum ;

PRIVATE>

: y2025day03 ( str -- )
  string>lines [ [ 48 - ] map { } like ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
