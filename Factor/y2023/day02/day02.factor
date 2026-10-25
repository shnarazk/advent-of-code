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

: mybag ( -- hashmap ) H{ { "red" 12 } { "green" 13 } { "blue" 14 } } ; inline

: key-num ( hashmap key -- key-num ) swap dupd at* [ ] [ drop 0 ] if 2array ;

: >key-vals ( hashmap keys -- sequence ) [ dupd key-num ] map nip ;

: part1/union-bags ( bag1 bag2 -- merged-bag )
  2dup
  [ keys ] bi@ union
  '[ _ >key-vals ] bi@
  [ [ first2 ] bi@ nip max 2array ] 2map >hashtable
;

: part1/all<=? ( bag1 bag2 -- merged-bag )
  2dup
  [ keys ] bi@ union
  '[ _ >key-vals ] bi@
  [ [ second ] bi@ <= ] 2map [ ] all?
;

: part1/possible-game? ( tables -- ? )
  3 <hashtable> [ part1/union-bags ] reduce
  mybag part1/all<=?
;

: part1/game ( game -- number ) first2 part1/possible-game? [ ] [ drop 0 ] if ;

: part1 ( games -- number ) [ part1/game ] map sum ;

: part2/union-bags ( bag1 bag2 -- merged-bag )
  2dup
  [ keys ] bi@ union
  '[ _ >key-vals ] bi@
  [ [ first2 ] bi@ nip max 2array ] 2map >hashtable
;

: part2/possible-game ( tables -- number )
  3 <hashtable> [ part2/union-bags ] reduce
  values product
;

: part2/game ( game -- number ) second part2/possible-game ;

: part2 ( games -- number ) [ part2/game ] map sum ;

: parser ( string -- number-config )
  ":" split
  first2 [ " " split last string>number ] [ ";" split [ "," split >hashmap ] map ] bi*
  2array
;

PRIVATE>

: y2023day02 ( str -- )
  string>lines [ parser ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
