#!/usr/bin/env Factor
! Copyright (C) 2026 Narazaki, Shuji.
USING:
  accessors arrays assocs combinators colors command-line continuations
  environment formatting hashtables
  io io.encodings.utf8 io.files io.pathnames io.styles
  json kernel math math.parser namespaces prettyprint
  sequences splitting strings tools.time unicode
  aoc.y2026.day01
  aoc.y2026.day02
  aoc.y2026.day03
  ! aoc.y2025.day01
  ! aoc.y2025.day02
  ! aoc.y2025.day03
  ! aoc.y2025.day04
  ! aoc.y2025.day05
  ! aoc.y2025.day06
  ! aoc.y2025.day07
  ! aoc.y2025.day08
  ! aoc.y2025.day09
  ! aoc.y2025.day10
  ! aoc.y2025.day11
  ! aoc.y2024.day01
  ! aoc.y2024.day02
  ! aoc.y2024.day03
  ! aoc.y2024.day04
  ! aoc.y2024.day05
  ! aoc.y2024.day07
  ! aoc.y2023.day01
  ! aoc.y2023.day02
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

:: config>oracles ( config -- 2strings )
  [
    "misc/answers.json" base-dir prepend-path
    utf8 file-contents json>
    config year>> number>string swap at
    config day>> number>string swap at
    config alt>>
    dup empty?
    [ drop " " ]
    [ dup 1 cut swap "-" =
      [ nip ]
      [ drop ]
      if
    ]
    if
    swap at
    [ "part1" swap at ]
    [ "part2" swap at ]
    bi
    2array
  ]
  [ ... { "" "" } ]
  recover
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
        [ default-year swap first2 [ string>number ] [ ] bi* ]
        [ first2 [ string>number ] bi@ "" ]
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
    { { 2026 1 } [ y2026day01 ] }
    { { 2026 2 } [ y2026day02 ] }
    { { 2026 3 } [ y2026day03 ] }
    ! { { 2025 1 } [ y2025day01 ] }
    ! { { 2025 2 } [ y2025day02 ] }
    ! { { 2025 3 } [ y2025day03 ] }
    ! { { 2025 4 } [ y2025day04 ] }
    ! { { 2025 5 } [ y2025day05 ] }
    ! { { 2025 6 } [ y2025day06 ] }
    ! { { 2025 7 } [ y2025day07 ] }
    ! { { 2025 8 } [ y2025day08 ] }
    ! { { 2025 9 } [ y2025day09 ] }
    ! { { 2025 10 } [ y2025day10 ] }
    ! { { 2025 11 } [ y2025day11 ] }
    ! { { 2024 1 } [ y2024day01 ] }
    ! { { 2024 2 } [ y2024day02 ] }
    ! { { 2024 3 } [ y2024day03 ] }
    ! { { 2024 4 } [ y2024day04 ] }
    ! { { 2024 5 } [ y2024day05 ] }
    ! { { 2024 7 } [ y2024day07 ] }
    ! { { 2023 1 } [ y2023day01 ] }
    ! { { 2023 2 } [ y2023day02 ] }
  }
  swap
  of
;

: run-solver ( oracles data quot: ( data -- answers ) -- )
  [ call
    [ unparse
      over "" =
      [ nip ]
      [ swap over = "✅" "❎" ? "%s %s" sprintf ]
      if ]
    2map
    first2 ]
  benchmark 1_000_000.0 /
  "Part1: %s, Part2: %s (%.2f msec.)\n" printf
;

PRIVATE>

: run-aoc ( -- )
  args>config
  dup config>print
  [ config>oracles ] [ config>data ] [ config>solver ] tri
  dup
  [ run-solver ]
  [ 3drop "Can't dispatch" print ]
  if
;

MAIN: run-aoc
