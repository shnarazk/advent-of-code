#!/usr/bin/env Factor
! Copyright (C) 2022 Your name.
! See https://factorcode.org/license.txt for BSD license.
USING: advent-of-code-2023 combinators formatting io kernel
       math math.parser prettyprint sequences splitting unicode ;
IN: test

: split-line ( string -- lines ) "\n" split [ "" = ] reject ;

: part1/line ( line -- number )
  [ digit? ] filter
  [ first ] [ last ] bi
  [ CHAR: 0 - ] bi@
  swap 10 * +
;

: transform ( substring -- letter )
  {
    { [ dup "" = ] [ drop CHAR: A ] }
    { [ dup " " append 0 "one"   swapd subseq-starts-at? ] [ drop CHAR: 1 ] }
    { [ dup " " append 0 "two"   swapd subseq-starts-at? ] [ drop CHAR: 2 ] }
    { [ dup " " append 0 "three" swapd subseq-starts-at? ] [ drop CHAR: 3 ] }
    { [ dup " " append 0 "four"  swapd subseq-starts-at? ] [ drop CHAR: 4 ] }
    { [ dup " " append 0 "five"  swapd subseq-starts-at? ] [ drop CHAR: 5 ] }
    { [ dup " " append 0 "six"   swapd subseq-starts-at? ] [ drop CHAR: 6 ] }
    { [ dup " " append 0 "seven" swapd subseq-starts-at? ] [ drop CHAR: 7 ] }
    { [ dup " " append 0 "eight" swapd subseq-starts-at? ] [ drop CHAR: 8 ] }
    { [ dup " " append 0 "nine"  swapd subseq-starts-at? ] [ drop CHAR: 9 ] }
    [ first ]
  }
  cond
;

: part2/line ( line -- number )
  dup length <iota> >array [ dupd tail transform ] map
  [ digit? ] filter
  [ first ] [ last ] bi
  [ CHAR: 0 - ] bi@
  swap 10 * +
  swap drop
;

: part1 ( data -- number ) split-line [ part1/line ] map sum ;
: part2 ( data -- number ) split-line [ part2/line ] map sum ;

: day01 ( -- ) 1 day>data [ part1 ] [ part2 ] bi [ pprint "" print ] bi@ ;

! run as
! $ Factor -run=test target-file
MAIN: day01
