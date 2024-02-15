#!/usr/bin/env Factor
! Copyright (C) 2022 Your name.
! See https://factorcode.org/license.txt for BSD license.
USING: command-line io io.encodings.utf8 io.files kernel math math.parser namespaces sequences ;
USING: advent-of-code-2023 ;
IN: test

! <PRIVATE PRIVATE>

: parse ( something -- ) utf8 file-contents print ;

: read-and-parse ( -- )
  command-line get dup length
  zero? [ drop "test.factor" ] [ first ] if
  parse
  ! 1 "" target-data
  base-dir
  print
  1 "" target-data
  print
;

! run as
! $ Factor -run=test target-file
MAIN: read-and-parse

