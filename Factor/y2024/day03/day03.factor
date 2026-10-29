USING:
  arrays combinators io kernel math math.parser
  prettyprint regexp sequences splitting strings
  aoc.lib.parser
;
IN: aoc.y2024.day03

<PRIVATE

: part1 ( line -- number )
  R/ mul\((\d+),(\d+)\)/
  all-matching-slices
  [ >string
    3 tail "(,)" split [ "" = ] reject [ string>number ] map
    product ] map
  sum
; inline

: part2 ( line -- number )
  R/ (mul\((\d+),(\d+)\)|do\(\)|don't\(\))/
  all-matching-slices
  [ >string
    { { "do()" [ t ] }
      { "don't()" [ f ] }
      [ 3 tail "(,)" split [ "" = ] reject [ string>number ] map product ]
    }
    case
  ] map
  { t 0 }
  [ { { t [ t 0 pick set-nth ] }
      { f [ f 0 pick set-nth ] }
      [ [ first2 ] dip pick [ + ] [ drop ] if 2array ] }
    case
  ]
  reduce
  second
; inline

PRIVATE>

: y2024day03 ( str -- )
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
