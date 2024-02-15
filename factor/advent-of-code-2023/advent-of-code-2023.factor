! Copyright (C) 2022 Your name.
! See https://factorcode.org/license.txt for BSD license.
USING: environment formatting io.pathnames sequences ;
IN: test

! <PRIVATE
: base-dir ( -- path ) "AOC_DIR" os-env ; 
! PRIVATE>

! : parse ( something -- ) utf8 file-contents print ;

: target-data ( day alt -- string )
  drop ! for now
  "input-%02d.txt" sprintf
  { "data" "2023" } base-dir [ append-path ] reduce
  prepend-path
;

