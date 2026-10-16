USING:
  arrays combinators io kernel math prettyprint sequences splitting unicode
  aoclib.parser
;
IN: y202X.day0X

<PRIVATE

: part1/line ( line -- number )
  drop 1
; inline

! { } [  ] unit-test

: part2/line ( line -- number )
  drop 2
; inline

: part1 ( data -- number ) [ part1/line ] map sum ;
: part2 ( data -- number ) [ part2/line ] map sum ;

PRIVATE>

: y202Xday0X ( str -- )
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;
