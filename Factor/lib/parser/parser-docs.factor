USING: help.markup help.syntax sequences strings ;
IN: aoc.lib.parser

HELP: string>lines
  { $values { "string" string } { "lines" { $sequence string } } }
  { $description "文字列を改行で分割する" }
;
