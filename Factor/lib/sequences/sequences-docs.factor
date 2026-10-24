USING: arrays help.markup help.syntax math quotations sequences strings ;
IN: aoc.lib.sequences

HELP: window2
  { $values { "seq" sequence } { "zipped-seq" { $sequence pair } } }
  { $description "Rustのwindows(2)に対応" }
;

HELP: satisfying-indices
  { $values
    { "sequence" sequence }
    { "quot" quotation }
    { "indices" { $sequence number } } }
  { $description "! `quot: ( x -- ? )`を満たす要素のix sequenceを返す
" }
;

HELP: unsatisfying-indices
  { $values
    { "sequence" sequence }
    { "quot" quotation }
    { "indices" { $sequence number } } }
  { $description "! `quot: ( x -- ? )`を満たさない要素のix sequenceを返す
" }
;
