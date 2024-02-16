! Copyright (C) 2022 Your name.
! See https://factorcode.org/license.txt for BSD license.
USING: command-line environment formatting io.encodings.utf8 io.files io.pathnames kernel math namespaces prettyprint sequences ;
IN: advent-of-code-2023

<PRIVATE
: base-dir ( -- path ) "AOC_DIR" os-env ; 
PRIVATE>

: target-data ( alt day -- string )
  swap
  dup length zero?
  [ drop "input-day%02d.txt" sprintf ]
  [ "input-day%02d-%s.txt" sprintf ]
  if
  { "data" "2023" } base-dir [ append-path ] reduce
  prepend-path
;

: day>data ( n -- string )
  command-line get dup length
  zero? [ drop "" ] [ first ] if
  swap target-data
  utf8 file-contents
;
