#!/usr/bin/env Factor
! Copyright (C) 2022 Your name.
! See https://factorcode.org/license.txt for BSD license.
USING: advent-of-code-2023 formatting io kernel math math.parser
       prettyprint sequences splitting ;
IN: test

: part1-process ( line -- number ) print 1 ;

: part1 ( data -- something )
  "\n" split [ "" = ] reject
  [ part1-process ] map sum
;

: part2 ( data -- something ) drop "?" ;

: day01 ( -- ) 1 day>data [ part1 ] [ part2 ] bi [ pprint "" print ] bi@ ;

! run as
! $ Factor -run=test target-file
MAIN: day01
