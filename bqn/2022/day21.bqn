Solve ⇐ {env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  dict ← {
    table ⇐ ⍉>{2=≠𝕩 ? ⟨⊑𝕩,•BQN 1⊑𝕩⟩ ; ⟨⊑𝕩,1↓𝕩⟩}¨" :"⊸lib.Tokenize¨data
    Search ⇐ {((⊏table)⊐⋈𝕩)⊑1⊏table}
    Set ⇐ {table ↩ 𝕩⌾(((⊏table)⊐⋈𝕨)⊸⊑1⊸⊏)table}
  }
  Op ← {"-"≡𝕨 ? -´𝕩 ; "+"≡𝕨 ? +´𝕩 ; "*"≡𝕨 ? ×´𝕩 ; "/"≡𝕨 ? ⌊÷´𝕩 ; 𝕨!0}
  Eval ← {E 𝕩 : {⟨l,o,r⟩ : o Op E¨l‿r ; 𝕩}dict.Search 𝕩}
  # "search root" lib.Debug dict.Search "root"
  {
    1=part ? Eval "root" ;
    2=part ?
      l‿o∞‿r ← dict.Search "root"
      Seek ← {lower S upper :
        !lower<upper
        "humn" dict.Set mid ← ⌊2÷˜lower+upper
        lib.Progress lower‿mid‿upper∾-´vals ← l ⋈○Eval r
        {𝕨>𝕩 ? mid S upper ; 𝕨<𝕩 ? lower S mid ; mid}´vals
      }
      -⊸Seek 2⋆50
  }
}
