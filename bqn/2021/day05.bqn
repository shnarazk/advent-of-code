Solve ⇐ {env‿part 𝕊 data : 
  util ← •Import "/util.bqn"∾˜ "," env.Var⌾⋈ "BQN_LIB"
  "" util.Debug 10↑segments ← ⥊⥊<˘∘‿2⥊<˘∘‿2⥊∾{x1‿y1‿x2‿y2 : (x1=x2)∨(y1=y2)}¨⊸/util.ParseInt¨¨", ->"⊸util.Tokenize¨data
  "" util.Debug min‿max ← (⌊´⋈⌈´)∾segments
  "" util.Debug 10↑segments (-⟜min)¨¨ ↩
  Seq ← ⥊·⋈⌜´·>¨·(⊢+↕¨∘¬)´¨·<˘·∨˘·⍉>
  {
    1=part ? +´1<⥊((max¬min)↑0){seg 𝕊 m : 1⊸+⌾((Seq seg)⊸⊑)m}´segments ;
    0
  }
}