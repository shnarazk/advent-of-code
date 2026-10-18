USING:
  arrays assocs combinators io kernel math math.parser prettyprint sequences
  sorting splitting unicode
  aoclib.parser
;
IN: y2024.day01

<PRIVATE

: part1 ( keys values -- number ) [ sort ] bi@ [ - abs ] 2map sum ;

: part2 ( keys values -- number )
  H{ }
  [ over inc-at ]
  reduce
  swap
  [  ! ( hashmap key )
    2dup ! ( hashmap key hashmap key )
    of
    dup f = [ drop drop 0 ] [ * ] if
  ] map
  sum
  nip
;

PRIVATE>

: y2024day01 ( str -- )
  string>lines
  [ " " split [ empty? not ] filter [ string>number ] map ] map
  { { } { } }
  [ [ first2 ] bi@ swapd [ suffix ] 2bi@ { } 2sequence ]
  reduce
  first2
  [ part1 ] [ part2 ] 2bi
  [ pprint "" print ] bi@
;
