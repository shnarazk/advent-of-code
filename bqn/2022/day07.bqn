 Solve ⇐ {env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜∾env.Var<"BQN_LIB"
  session ← (⟨⟩⊸≢)¨⊸/{(⟨⟩⊸≢)¨⊸/" "((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩}¨"$"((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)∾(" "⊸∾˜)¨data
  dirs ← ⟨⟩
  Traverse ← {io 𝕊 pwd :
    {
      ⟨"cd"⟩≡io      ? pwd ↩ ⟨"/"⟩ ;
      ⟨"cd",".."⟩≡io ? pwd (¯1+≠)⊸↑↩ ;
      "cd"≡⊑io       ? pwd (<1⊑io)⊸(∾˜)↩ ;
      "ls"≡⊑io ?
        total ← 0
        {"dir"≢𝕨 ? total (•BQN 𝕨)⊸+↩ ⋄  @ ; @}´˘(2⊸|)¨∘⊒˜⊸/2↕io
        dirs ⟨⟨∾pwd, total⟩⟩⊸∾ ↩
    }
    {0=≠pwd ? ⟨"/"⟩; pwd}
  }
  ⟨⟩Traverse´⌽session
  ComponentsOf ← {(𝕩˙(lib.StartsWith˜)⊑)¨⊸/dirs}
  eachDir ← (⊑⋈(+´∘((1⊸⊑)¨)∘ComponentsOf⊑))¨dirs
  {
    1=part ? +´(1⊸⊑)¨(100000≥1⊸⊑)¨⊸/eachDir
    ;
      "free" lib.Debug free ← 70000000-1⊸⊑⊑("/"⊸≡⊑)¨⊸/eachDir
      "to be freed" lib.Debug required ← 30000000-free
      ⊑⊑∧(required⊸<⊑)¨⊸/lib.Swap¨eachDir
  }
}