Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  time ← util.ParseInt⊑data
  ids ← (≠)◶⟨⊢,⊑⟩¨util.ParseInts¨ "," util.Tokenize 1⊑data
  valids ← ⟨⟩⊸≢¨⊸/ids
  {
    1=part ? ((valids⊸(⊑˜)·⊑⍋)×((⊑⍋)⊸⊑))time-˜×⟜(time⊸(⌈∘÷))valids ;
    Chinese ← {bq‿br 𝕊 aq‿ar :
      n ← aq÷˜(aq⊸+)•_while_(1≠bq⊸|)0
      nar‿nbr ← bq|n×ar‿br
      m ← (nar<nbr)◶⟨bq+nbr-nar,nbr-nar⟩@
      ⟨aq×bq,util.Progress ar+m×aq⟩
    }
    # ! 8=1⊑Chinese´⟨5‿3,3‿2⟩ !23=1⊑Chinese´⟨5‿3,3‿2,2‿7⟩
    1⊑Chinese´∧⥊{𝕨>𝕩 ? <⟨𝕨,𝕨-𝕩⟩ ; <⟨𝕨,𝕨|𝕩-˜𝕨×𝕩⟩}´˘⍉valids≍remains ← (⟨⟩⊸≢¨ids)/↕≠ids
  }
}
