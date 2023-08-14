Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  points‿flips ← (((1+¯2⊸×)×+`)(⟨⟩⊸≡¨))⊸⊔ data
  points ↩ util.ParseInts¨ points
  flips ↩ ({𝕊 a‿p : ("yx"⊐a)∾util.ParseInt p}·2⊸↓" ="⊸util.Tokenize)¨flips
  ≠points{axis‿m 𝕊 ps : ⍷{⟨𝕨-2×(1=axis)×m(<×|)𝕨,𝕩-2×(0=axis)×m(<×|)𝕩⟩}´¨ps}´⌽util.Debug ⋈⊑flips
}
