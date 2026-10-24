USING:
  arrays help.markup help.syntax kernel math math.matrices sequences splitting
  aoc.lib.matrices.private
;
IN: aoc.lib.matrices

HELP: matrix-indices
  { $values { "matrix" matrix } { "array" { $sequence pair } } }
  { $description "List of indices (pairs) of the given matrix." }
;

HELP: 4neighbors-indices
  { $values { "matrix" matrix } { "matrix" matrix } }
  { $description "A memoized function returning a matrix of a list of each four neighbors' indices (list of pairs)" }
;

HELP: 8neighbors-indices
  { $values { "matrix" matrix } { "matrix" matrix } }
  { $description "A memoized function returning a matrix of a list of each eight neighbors' indices (list of pairs)" }
;

HELP: 8neighbors-values
  { $values { "matrix" matrix } { "matrix" matrix } }
  { $description "Matrix of a list of each eight neighbors' values" }
;
