USING: arrays sequences ;
USING:
  arrays
  combinators
  io kernel
  math
  prettyprint
  sequences
  splitting
  unicode
  aoc.lib.parser
;
IN: aoc.y2025.day10

<PRIVATE

: apply-button ( state button -- state' )
  [ xor ] 2map
;

: spec ( goal-buttons-_ -- goal actions )
  first2               ! ( goal buttons )
  [ dup length f <array> ] dip
  [                         ! template ( indices )
    [ dup clone ] dip       ! ( template' indices )
    [ t swap pick set-nth ] each
  ] map
  nip
; inline

: solve ( goal actions -- number )
  2dup 2array ...
  2drop
  1
;

: part1 ( data -- number ) [ spec solve ] map sum ;

PRIVATE>

: y2025day10 ( str -- )
  string>lines
  [ "]" split
    first2
    [ >array rest [ CHAR: # = ] map ]
    [ "{" split
      first2
      [ [ CHAR: \u000020 = ] reject
        "()" split [ "" = ] reject
        [ "," split [ string>number ] map ] map ]
      [ but-last "," split [ string>number ] map ]
      bi* ]
    bi*
    3array ]
  map
  [ part1 ] [ drop 0 ] bi
  [ pprint "" print ] bi@
;
