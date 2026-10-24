USING:
  arrays help.markup help.syntax kernel math math.matrices sequences splitting
  aoc.lib.matrices.private
;
IN: aoc.lib.parser

HELP: string>lines
  { $values { "string" string } { "lines" { $sequence string } } }
  { $description "文字列を改行で分割する" }
;
