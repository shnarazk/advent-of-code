USING: arrays assocs kernel math quotations sequences
;
IN: aoc.lib.sequences

: window2 ( seq -- zipped-seq ) dup [ but-last ] [ rest ] bi* zip ;

: satisfying-indices ( sequence quot: ( x -- ? ) -- indices )
  [ dup [ length <iota> ] dip ] dip ! ( iota seq quot )
  '[ @ [ dup drop ] [ drop f ] if ] 2map
  [ f = ] reject
;

: unsatisfying-indices ( sequence quot: ( x -- ? ) -- indices )
  [ dup [ length <iota> ] dip ] dip ! ( iota seq quot )
  '[ @ not [ dup drop ] [ drop f ] if ] 2map
  [ f = ] reject
;

: !satisfies ( sequence quot: ( x -- ? ) -- indices )
  swap
  dup length <iota> ! ( quot seq iota )
  spin              ! ( iota seq quot )
  map [ [ drop -1 ] when ] 2map
  [ 0 >= ] filter
; deprecated
