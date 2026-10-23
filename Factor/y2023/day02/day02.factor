USING: arrays assocs combinators hashtables io kernel math math.parser
  prettyprint sequences splitting
  aoc.lib.parser
;
IN: aoc.y2023.day02

<PRIVATE

: >hashmap ( sequence -- hathmap )
  100 <hashtable>
  [ over [ [ CHAR: \u000020 = ] trim " " split first2 swap string>number ] dip set-at ]
  reduce
;

: parser ( string -- number-config )
  ":" split
  first2 [ " " split last string>number ] [ ";" split [ "," split >hashmap ] map ] bi*
  2array dup ...
;

: part1/line ( line -- number )
  drop 1
; inline

: part2/line ( line -- number )
  drop 2
; inline

: part1 ( data -- number ) [ part1/line ] map sum ;
: part2 ( data -- number ) [ part2/line ] map sum ;

PRIVATE>

: y2023day02 ( str -- )
  string>lines [ parser ] map
  dup ...
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
