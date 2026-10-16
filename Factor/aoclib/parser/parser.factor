USING: arrays combinators kernel math sequences splitting unicode ;
IN: aoclib.parser

: string>lines ( string -- lines ) "\n" split [ "" = ] reject ; inline
