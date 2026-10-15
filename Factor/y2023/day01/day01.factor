#!/usr/bin/env Factor
! Copyright (C) 2022 Your name.
! See https://factorcode.org/license.txt for BSD license.
USING: arrays combinators command-line environment formatting
  io io.encodings.utf8 io.files io.pathnames
  kernel math math.parser namespaces prettyprint
  sequences splitting tools.time unicode
  y2023
;

IN: y2023.day01

<PRIVATE
: split-line ( string -- lines ) "\n" split [ "" = ] reject ;

: part1/line ( line -- number )
  [ digit? ] filter
  [ first ] [ last ] bi
  [ CHAR: 0 - ] bi@
  swap 10 * +
;

: transform ( substring -- letter )
  " " append
  {
    { [ dup " " = ] [ drop CHAR: A ] }
    { [ dup 0 "one"   swapd subseq-starts-at? ] [ drop CHAR: 1 ] }
    { [ dup 0 "two"   swapd subseq-starts-at? ] [ drop CHAR: 2 ] }
    { [ dup 0 "three" swapd subseq-starts-at? ] [ drop CHAR: 3 ] }
    { [ dup 0 "four"  swapd subseq-starts-at? ] [ drop CHAR: 4 ] }
    { [ dup 0 "five"  swapd subseq-starts-at? ] [ drop CHAR: 5 ] }
    { [ dup 0 "six"   swapd subseq-starts-at? ] [ drop CHAR: 6 ] }
    { [ dup 0 "seven" swapd subseq-starts-at? ] [ drop CHAR: 7 ] }
    { [ dup 0 "eight" swapd subseq-starts-at? ] [ drop CHAR: 8 ] }
    { [ dup 0 "nine"  swapd subseq-starts-at? ] [ drop CHAR: 9 ] }
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

PRIVATE>

: y2023day01 ( str -- )
  [ part1 ] [ part2 ] bi
  [ pprint "" print ] bi@
;

! run as
! $ Factor -run=test target-file
! MAIN: y2023day01
