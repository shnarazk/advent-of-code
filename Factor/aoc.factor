#!/usr/bin/env Factor
! Copyright (C) 2026 Narazaki, Shuji.
! See https://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs combinators command-line environment formatting
  colors hashtables
  io io.encodings.utf8 io.files io.pathnames io.styles
  kernel math math.parser namespaces prettyprint
  sequences splitting tools.time unicode
  aoc.y2025.day01
  aoc.y2025.day02
  aoc.y2025.day03
  aoc.y2025.day04
  aoc.y2025.day05
  aoc.y2024.day01
  aoc.y2024.day02
  aoc.y2023.day01
;
IN: aoc

<PRIVATE

TUPLE: config year day alt ;

: config-new ( year day alt -- config )
  config new
  swap >>alt
  swap >>day
  swap >>year
;

! { 2025 } [ 2025 1 "" config-new year>> ] unit-test

: base-dir ( -- path ) "AOC_DIR" os-env ;

: default-year ( -- n ) 2025 ;

: config>target ( config -- string )
  [ year>> ] [ day>> ] [ alt>> ] tri
  "data/%04d/input-day%02d%s.txt" sprintf
  base-dir prepend-path
;

: config>print ( config -- )
  [ year>> ] [ day>> ] [ alt>> ] tri
  "data/%04d/input-day%02d%s.txt\n" sprintf
   "red" named-color foreground associate format
;

: target>data ( target -- string ) utf8 file-contents ;

: config>data ( config -- string ) config>target target>data ;

: args>config ( -- config )
  command-line get dup length
  {
    { [ dup 0 = ] [ drop drop default-year 1 "" ] }
    { [ dup 1 = ] [ drop first string>number default-year swap "" ] }
    { [ dup 2 = ]
      [
        drop dup last first CHAR: - =
        [ default-year swap dup first string>number swap second ]
        [ dup first string>number swap second string>number "" ]
        if
      ]
    }
    [ drop [ first string>number ] [ second string>number ] [ last ] tri ]
  }
  cond
  config-new
;

: args>data ( -- string ) args>config config>target target>data ;

: config>solver ( config -- function )
  [ year>> ] [ day>> ] bi 2array
  H{
    { { 2025 1 } [ y2025day01 ] }
    { { 2025 2 } [ y2025day02 ] }
    { { 2025 3 } [ y2025day03 ] }
    { { 2025 4 } [ y2025day04 ] }
    { { 2025 5 } [ y2025day05 ] }
    { { 2024 1 } [ y2024day01 ] }
    { { 2024 2 } [ y2024day02 ] }
    { { 2023 2 } [ y2023day01 ] }
  }
  swap
  of
;

: run-solver ( ? quot: ( ? -- ) -- ) call ;

PRIVATE>

: run-aoc ( -- )
  args>config [ config>print ] [ config>data ] [ config>solver ] tri
  [ run-solver ] benchmark
  1000000.0 / "%.2f msec" printf
;

MAIN: run-aoc
