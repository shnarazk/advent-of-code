USING:
  arrays
  combinators
  hash-sets
  heaps
  io
  kernel
  math
  math.parser
  prettyprint
  sequences
  sets
  splitting
  unicode
  aoc.lib.parser
;
IN: aoc.y2025.day10

<PRIVATE

: apply-button ( state button -- state' ) [ xor ] 2map ; inline

:: A*-search/step ( goal actions to-visit visited -- number )
  to-visit heap-empty?
  [ -1 ]
  [ to-visit heap-pop
    over goal =                         ! ( state count ? )
    [ nip ]
    [ over visited in?
      [ 2drop goal actions to-visit visited A*-search/step ]
      [ over visited adjoin
        1 +                                    ! ( state count+1 )
        actions [ pick swap apply-button ] map ! ( state count+1 next-states )
        [ visited in? ] reject
        [ over to-visit heap-push ] each
        2drop goal actions to-visit visited A*-search/step
      ]
      if
    ]
    if
  ]
  if
; recursive

: A*-search ( goal actions init-state  -- state )
  <min-heap> swap 0 pick heap-push
  HS{ }
  A*-search/step
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
  dup first [ drop f ] map
  A*-search
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
