USING:
  arrays combinators io kernel math math.matrices prettyprint
  sequences splitting unicode
  aoclib.matrices aoclib.parser
;
IN: y2025.day04

<PRIVATE

: >0/1 ( ? -- 0/1 ) [ 1 ] [ 0 ] if ;

: next ( matrix -- matrix )
  8neighbors-values
  [ sum 4 < >0/1 ] matrix-map
;

: part1 ( matrix -- number )
  dup next
  m*
  [ sum ] map sum
;

: next/mask ( matrix -- matrix )
  8neighbors-values
  [ sum 4 >= >0/1 ] matrix-map
;

: part2/step ( matrix -- matrix )
  dup next/mask
  m*
;

: >fixpoint ( val state quot-eval -- state )
  swap over          ! ( val quot-eval state quot-eval )
  first2 -rot        ! ( val quot-eval eval state quot )
  call( x -- x )     ! ( val quot-eval eval state' )
  dup                ! ( val quot-eval eval state' state' )
  rot                ! ( val quot-eval state' state' eval )
  call( x -- x )     ! ( val quot-eval state' val' )
  rotd               ! ( quot-eval state' val val' )
  swap over =        ! ( quot-eval state' val' ? )
  [ drop nip ]       ! ( state' )
  [ spin >fixpoint ] ! ( val' state' quot-eval )
  if
; recursive

: part2 ( matrix -- matrix )
  dup [ sum ] map sum
  swap
  0 swap [ [ part2/step ] [ [ sum ] map sum ] ] >fixpoint
  [ sum ] map sum
  -
;

PRIVATE>

: y2025day04 ( str -- )
  string>lines [ { } like [ CHAR: @ = >0/1 ] map ] map
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
