Solve ⇐ {env‿part 𝕊 data :
  util ← •Import"/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  util.Debug (××1+|) 4
  util.Debug (××1+|) ¯4
  {
    1=part ?
      Parse ← {
        digits ← ⟨⟩
        levels ← ⟨⟩
        0{
           '[' 𝕊 lv : 1+|lv ;
           ',' 𝕊 lv : -lv ;
           ']' 𝕊 lv : ¯1+|lv ;
           𝕨 𝕊 lv : ('0'≤𝕨)∧'9'≥𝕨 ?
             digits ∾⟜(util.ParseInt⋈𝕨) ↩
             levels ∾⟜lv ↩
             lv ;
            !0
        }´⌽𝕩
        digits⋈levels
      }
    ≢Parse¨data
    ;
      0
  }
}
