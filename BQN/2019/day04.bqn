Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt¨∘("-"⊸util.Split)∘⊑ ↩
  Digits ← {𝕊 0 : ⟨⟩ ; 𝕊 n : ⟨10|n⟩∾˜𝕊 10⌊∘(÷˜)n}
  cands ← ((∧´≤´˘)∧(∨´=´˘))∘(2⊸↕)¨⊸/Digits¨(⊑+↕∘(¬˜´))data
  {
    1=part ? ≠cands ;
    Train ← {0<0{𝕩⌈𝕨-1}`𝕨×∾⟜((-¬𝕨)↑0)(1=≠∘⍷)˘𝕨↕𝕩}
    +´(∨´(2⊸Train)⊸∧⟜(¬3⊸Train))¨cands
  }
}
