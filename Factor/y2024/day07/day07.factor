USING:
  arrays
  ! accessors
  combinators
  hash-sets
  io
  kernel
  math
  math.parser
  prettyprint
  sequences
  sets
  splitting
  ! unicode
  aoc.lib.parser
;
IN: aoc.y2024.day07

<PRIVATE

:: part1/recursor ( goal states elements -- ? )
  elements empty?
  [ f ]
  [ elements first
    states members
    HS{ } clone
    [ pick 2dup [ * ] [ + ] 2bi*
      dup goal <= [ pick adjoin ] [ drop ] if
      dup goal <= [ over adjoin ] [ drop ] if ]
    reduce
    nip
    goal over in?
    [ drop t ]
    [ members goal swap elements rest part1/recursor ]
    if ]
  if
; recursive

:: part1/line ( goal elements -- number )
  goal elements 1 cut
  [ first 1array ] dip
  part1/recursor
  goal 0 ?
; inline

: part1 ( data -- number ) [ first2 part1/line ] map sum ;

: part2/line ( line -- number )
  drop 2
; inline

: part2 ( data -- number ) [ part2/line ] map sum ;

PRIVATE>

: y2024day07 ( str -- )
  string>lines
  [ ":" split first2
    [ string>number ]
    [ " " split [ empty? ] reject [ string>number ] map ]
    bi*
    2array ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
