USING:
  arrays combinators hash-sets io kernel math math.functions math.parser
  prettyprint sequences sets splitting
  aoc.lib.parser
;
IN: aoc.y2024.day07

<PRIVATE

:: part1/recursor ( goal states elements -- ? )
  elements empty?
  [ goal states in? ]
  [ elements first
    states members
    HS{ } clone
    [ pick 2dup [ * ] [ + ] 2bi*
      dup goal <= [ pick adjoin ] [ drop ] if
      dup goal <= [ over adjoin ] [ drop ] if ]
    reduce
    nip
    members goal swap elements rest part1/recursor ]
  if
; recursive

:: part1/line ( goal elements -- number )
  goal elements 1 cut
  [ first 1array ] dip
  part1/recursor
  goal 0 ?
; inline

: part1 ( data -- number ) [ first2 part1/line ] map sum ;

: | ( a b -- a<b )
 dup 0 = f assert=
 dup log10 >integer 1 + 10 swap ^ rot * +
; inline

:: part2/recursor ( goal states elements -- ? )
  elements empty?
  [ goal states in? ]
  [ elements first
    states members
    HS{ } clone
    [ pick over + dup goal <= [ pick adjoin ] [ drop ] if
      pick over * dup goal <= [ pick adjoin ] [ drop ] if
      pick over swap | dup goal <= [ pick adjoin ] [ drop ] if
      drop ]
    reduce
    nip
    members goal swap elements rest part2/recursor ]
  if
; recursive

:: part2/line ( goal elements -- number )
  goal elements 1 cut
  [ first 1array ] dip
  part2/recursor
  goal 0 ?
; inline

: part2 ( data -- number ) [ first2 part2/line ] map sum ;

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
