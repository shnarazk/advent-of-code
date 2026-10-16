#!/usr/bin/env Factor
! Copyright (C) 2026 Narazaki, Shuji.
! See https://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs combinators command-line environment formatting
  io io.encodings.utf8 io.files io.pathnames
  kernel math math.parser namespaces prettyprint
  sequences splitting tools.time unicode
  y2023.day01
  y2025.day01
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

: target>data ( target -- string ) utf8 file-contents ;

: config>data ( config -- string ) config>target target>data ;

: args>config ( -- config )
  command-line get dup length
  {
    { [ dup 0 = ] [ drop drop default-year 1 "" config-new ] }
    { [ dup 1 = ]
      [ drop first string>number default-year swap "" config-new ] }
    { [ dup 2 = ]
      [
        drop dup last first CHAR: - =
        [
          default-year
          swap dup first string>number
          swap second
          config-new
        ]
        [
          dup first string>number
          swap second string>number ""
          config-new
        ]
        if
      ]
    }
    [ drop
      [ first string>number ] [ second string>number ] [ last ] tri config-new ]
  }
  cond
;

: args>data ( -- string ) args>config config>target target>data ;

: config>solver ( config -- function )
  [ year>> ] [ day>> ] bi { } 2sequence
  H{
    { { 2025 1 } [ y2025day01 ] }
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
