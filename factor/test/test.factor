! Copyright (C) 2022 Your name.
! See https://factorcode.org/license.txt for BSD license.
USING: command-line io kernel namespaces sequences ;
IN: test

! <PRIVATE PRIVATE>

: parse ( something -- ) print ;

: read-and-parse ( -- ) command-line get first parse ;

! run as
! $ Factor -run=test target-file
MAIN: read-and-parse

