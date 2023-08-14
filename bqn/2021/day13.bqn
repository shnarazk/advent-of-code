Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  points‿flips ← (((1+¯2⊸×)×+`)(⟨⟩⊸≡¨))⊸⊔ data
  points ↩ util.ParseInts¨ points
  flips ↩ ({𝕊 a‿p : ("yx"⊐a)∾util.ParseInt p}·2⊸↓" ="⊸util.Tokenize)¨flips
  {
    1=part ? ≠points{axis‿m 𝕊 ps : ⍷{⟨𝕨-2×(1=axis)×𝕨(>×-)m,𝕩-2×(0=axis)×𝕩(>×-)m⟩}´¨ps}´⌽⋈⊑flips ;
    p ← points{axis‿m 𝕊 ps : ⍷{⟨𝕨-2×(1=axis)×𝕨(>×-)m,𝕩-2×(0=axis)×𝕩(>×-)m⟩}´¨ps}´⌽flips
    shape ← ⌽1+⌈´˘⍉>p
    (shape↑' '){x‿y 𝕊 m : '#'⌾(y‿x⊸⊑)m}´p
  }
}
