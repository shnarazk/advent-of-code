USING: help help.markup help.syntax math strings sequences
  aoc.y2025.day06.private
;
IN: aoc.y2025.day06

HELP: y2025day06
{ $values { } }
{ $description "" } ;

ARTICLE: "aoc.y2025.day06" "aoc.y2025.day06"
  "入力を2次元文字配列と見なすと転置行列に対してもparseしなけばならない問題。 "
  "他言語版と違ってparser combinatorsを使ってないので難易度が上がるわけではない。"
  $nl { $subsections part1 } "通常のparse"
  $nl { $subsections part1 } "転置させてからparse"
;

ABOUT: "aoc.y2025.day06"
