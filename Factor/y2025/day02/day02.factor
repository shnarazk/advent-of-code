USING: sequences kernel ;
USING:
  arrays combinators io kernel math math.parser prettyprint
  sequences sequences.repeating splitting unicode
  aoclib.parser
;
IN: y2025.day02

<PRIVATE

: 2repeat? ( number -- ? )
  number>string
  dup length 2 /i cut
  =
;

: part1/loop ( limit n -- number )
  2dup >=
  [ dup 2repeat? [ dup -rot 1 + part1/loop + ] [ 1 + part1/loop ] if ]
  [ 2drop 0 ]
  if
; recursive

: part1/line ( beg-end -- number ) first2 swap part1/loop ; inline

: div-m? ( n m -- n/m m ? ) [ /i ] [ [ nip ] [ mod zero? ] 2bi ] 2bi ; inline

: n-repeat? ( number -- ? )
  number>string
  dup length dup 2 /i <iota> [ 1 + ] map
  [ 2over rot                         ! ( string length string length n )
    div-m?                            ! ( string length string l/n n l%n? )
    [ swapd head swap repeat pick = ] ! ( string length l/n*string%n=string )
    [ 3drop f ] if
  ] any?
  2nip
; inline

: part2/loop ( limit n sum -- sum' )
  2over >=
  [ over n-repeat? [ [ drop 1 + ] [ + ] 2bi part2/loop ] [ swap 1 + swap part2/loop ] if ]
  [ 2nip ]
  if
; recursive

: part2/line ( beg-end -- number ) first2 swap 0 part2/loop ; inline

: part1 ( data -- number ) [ part1/line ] map sum ;
: part2 ( data -- number ) [ part2/line ] map sum ;

PRIVATE>

: y2025day02 ( str -- )
  "," split [ [ CHAR: \n = ] trim "-" split [ string>number ] map ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
