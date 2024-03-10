Solve ⇐ {env‿part 𝕊 data :
  util ← •Import"/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
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
  Add ← {wd‿wl 𝕊 xd‿xl : ⟨wd∾xd,(××1+|)¨wl∾xl⟩}
  Explode ← {𝕊 d‿l :
    ∨´ables ← ((=´∧(∧´4⊸≤))1‿¯1⊸×)˘2↕l ?
      "Explode" util.Debug ables
      target ← ables⊸⊐⌾⋈1
      "target" util.Debug target
      {0<target ? d (⊢+target⊑d)⌾((target-1)⊸⊑) ↩ ; @}
      {(≠l)>2+target ? d (⊢+(target+1)⊑d)⌾((target+2)⊸⊑) ↩ ; @}
      # substitude the pair
      d
      ;
    𝕩
  }
  Split ← {𝕊 xd‿xl : 𝕩}
  Combine ← {
    z ← 𝕨 Add 𝕩
    # Explode and Split
    z
  }
  {
    1=part ?
    l ← Parse¨data
    f ← ⊑l
    Explode "try explode" util.Debug f
    ;
      0
  }
}
