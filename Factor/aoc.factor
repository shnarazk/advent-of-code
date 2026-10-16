#!/usr/bin/env Factor
! Copyright (C) 2026 Narazaki, Shuji.
! See https://factorcode.org/license.txt for BSD license.
USING: arrays assocs combinators command-line environment formatting
  io io.encodings.utf8 io.files io.pathnames
  kernel math math.parser namespaces prettyprint
  sequences splitting tools.time unicode
  y2023.day01
;
IN: aoc

<PRIVATE

: base-dir ( -- path ) "AOC_DIR" os-env ;

: default-year ( -- n ) 2025 ;

: config>target ( config -- string )
  first3
  "data/%04d/input-day%02d%s.txt" sprintf
  base-dir prepend-path
;

: target>data ( target -- string ) utf8 file-contents ;

: config>data ( config -- string ) config>target target>data ;

: args>config ( -- config )
  command-line get dup length
  {
    { [ dup 0 = ] [ drop drop default-year 1 "" { } 3sequence ] }
    { [ dup 1 = ]
      [ drop first string>number default-year swap "" { } 3sequence ] }
    { [ dup 2 = ]
      [
        drop dup last first CHAR: - =
        [
          default-year
          swap dup first string>number
          swap second
          { } 3sequence
        ]
        [
          dup first string>number
          swap second string>number ""
          { } 3sequence
        ]
        if
      ]
    }
    [ drop unclip-last swap [ string>number ] map swap suffix ]
  }
  cond
;

: args>data ( -- string ) args>config config>target target>data ;

: config>solver ( config -- function )
  but-last
  H{
    { { 2023 1 } [ y2023day01 ] }
    { { 2023 2 } [ y2023day01 ] }
  }
  swap
  of
;

: run-solver ( ? quot: ( ? -- ) -- ) call ;

PRIVATE>

: run-aoc ( -- )
  args>config [ config>data ] [ config>solver ] bi
  [ run-solver ] benchmark
  1000000.0 / "%.2f msec" printf
;

MAIN: run-aoc
