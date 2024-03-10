sea_level ← ¯100
IndexOf ← {⊑(𝕨⊸=⊑⟜𝕩)¨⊸/⥊↕·≢𝕩}
Choose ← {other 𝕊 self :
  {
    self∧○(0⊸<)other    ? self⌊1+other ;
    (0<other)∧(other<∞) ? 1+other ;
    self
  }
}
MakeNeighbor ← {(⌽⍉)⍟(4-𝕩)∞⊸»˘(⌽⍉)⍟𝕩 𝕨}
Neighbors ← {𝕩⊸MakeNeighbor¨↕4}

Solve ⇐ {env‿part 𝕊 lines :
  util ← •Import"/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  visualize ← util.ParseInt "1" env.Var⌾⋈ "AOC_VISUALIZE"
  dump ← {
     visualize ?
      {t 𝕊 𝕩 :
        util.term.Up ≠𝕩
        Colorize ← {𝕩≥𝕨 ? 80‿(⌊255-255⌊⌊2500÷√𝕩)‿(⌊255⌊30×1.8⋆⁼𝕩) ; 100‿100‿100}
        {util.term.Outln∾{((t Colorize 𝕩) util.color.RGB 0)∾" "}¨𝕩 ⋄ ⟨⟩}˘𝕩
        𝕩
      } ;
    {𝕩}
  }
  shape ← (≠⋈(≠⊑))lines
  map ← (shape⊸⥊)∘(sea_level⊸+'a'⊸(-˜))∘∾lines
  start‿end ← (map⊸(IndexOf˜)sea_level⊸+∘-⟜'a')¨'S'‿'E'
  map⟨sea_level,sea_level+'z'-'a'⟩⌾(start‿end⊸⊑) ↩
  reachables ← {(≢map)⥊(¯1+⥊map)≤⥊𝕩}¨Neighbors map
  MaskedNeighbors ← reachables×{(𝕩⊸MakeNeighbor)¨↕4}

  n ← {1=part ? m ← 1˙⌾(start⊸⊑) map ; {sea_level=𝕩 ? 1 ; 𝕩}¨˘map}
  {visualize ? {𝕤⋄ •Show ""}⍟(≠map)@ ; @}
  n {0 Dump (Choose¨˘´⟜ MaskedNeighbors)𝕩}•_while_{0>end⊑𝕩} ↩
  {visualize ? •Out util.term.reset∾util.term.clear ; @}
  ¯1⊸+end⊸⊑n
}
