#!/usr/bin/env Factor
! Copyright (C) 2022 Your name.
! See https://factorcode.org/license.txt for BSD license.
USING: advent-of-code-2023 formatting io io.encodings.utf8 io.files
       kernel math math.parser sequences ;
IN: test

: day01 ( -- ) 1 day>data print ;

! run as
! $ Factor -run=test target-file
MAIN: day01

