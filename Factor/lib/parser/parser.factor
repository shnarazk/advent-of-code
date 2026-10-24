USING: kernel sequences splitting ;
IN: aoc.lib.parser

: string>lines ( string -- lines ) "\n" split [ "" = ] reject ; inline
