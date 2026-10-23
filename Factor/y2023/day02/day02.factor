USING: arrays assocs combinators hashtables io kernel
  math math.order math.parser prettyprint sequences sets splitting
  aoc.lib.parser
tools.test ;
IN: aoc.y2023.day02

<PRIVATE

: >hashmap ( sequence -- hashmap )
  3 <hashtable>
  [ over [ [ CHAR: \u000020 = ] trim " " split first2 [ string>number ] dip ] dip set-at ]
  reduce
;

: mybag ( -- hashmap )
  H{ { "red" 12 } { "green" 13 } { "blue" 14 } }
; inline

: key-num ( hashmap key -- key-num )
  swap dupd at* [ ] [ drop 0 ] if 2array
;

: >key-vals ( hashmap keys -- sequence )
  [ dupd key-num ] map nip
;

: union-bags ( bag1 bag2 -- merged-bag )
  2dup
  [ keys ] bi@ union
  [ >key-vals ] curry bi@
  [ [ first2 ] bi@ nip max 2array ] 2map >hashtable
;

: all<=? ( bag1 bag2 -- merged-bag )
  2dup
  [ keys ] bi@ union
  [ >key-vals ] curry bi@
  [ [ second ] bi@ <= ] 2map [ ] all?
;
: possible-game? ( tables -- ? )
  3 <hashtable> [ union-bags ] reduce
  mybag all<=?
;

: parser ( string -- number-config )
  ":" split
  first2 [ " " split last string>number ] [ ";" split [ "," split >hashmap ] map ] bi*
  2array
;

: part1/game ( game -- number ) first2 possible-game? [ ] [ drop 0 ] if ;

: part2/game ( game -- number )
  drop 2
; inline

: part1 ( games -- number ) [ part1/game ] map sum ;
: part2 ( games -- number ) [ part2/game ] map sum ;

PRIVATE>

: y2023day02 ( str -- )
  string>lines [ parser ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
