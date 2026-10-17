USING: help help.markup help.syntax math strings sequences y2025.day03.private ;
IN: y2025.day03

HELP: y2025day03
{ $values { } }
{ $description "数列の問題: 数列から指定された仕様の部分列を構成する。" } ;

HELP: maximize
  { $values { "line" sequence } { "depth" number } { "value" number } }
  { $description "解候補の列に数値を加えて最も大きな値を持つ解候補を返す" }
;
