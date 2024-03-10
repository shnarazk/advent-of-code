Solve ⇐ {env‿part 𝕊 data :
  math‿util ← •Import¨"/math.bqn"‿"/util.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  time ← util.ParseInt⊑data
  ids ← (≠)◶⟨⊢,⊑⟩¨util.ParseInts¨ "," util.Split 1⊑data
  valids ← ⟨⟩⊸≢¨⊸/ids
  {
    1=part ? ((valids⊸(⊑˜)·⊑⍋)×((⊑⍋)⊸⊑))time-˜×⟜(time⊸(⌈∘÷))valids ;
    1⊑math.CRT´∧⥊{𝕨>𝕩 ? <⟨𝕨,𝕨-𝕩⟩ ; <⟨𝕨,𝕨|𝕩-˜𝕨×𝕩⟩}´˘⍉valids≍remains ← (⟨⟩⊸≢¨ids)/↕≠ids
  }
}
