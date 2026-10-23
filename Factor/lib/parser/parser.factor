USING: arrays combinators kernel math sequences splitting unicode
;
IN: aoc.lib.parser

: string>lines ( string -- lines ) "\n" split [ "" = ] reject ; inline
