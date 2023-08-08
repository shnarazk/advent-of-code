Solve ⇐ {env‿part 𝕊 data : 
  util ← •Import "/util.bqn"∾˜ "," env.Var⌾⋈ "BQN_LIB"
  "dist" util.Debug dist ← 7↑/⁼ start ← util.ParseInt¨ "," util.Tokenize∾data
  days ← (2=part)⊑⟨80,256⟩
  {+´(1⊑𝕩)∾¯2↑𝕩}{n‿dist‿d7‿d8 : ⟨1+n,(d7⊸+)⌾(6⊸⊑)1⌽dist,d8,⊑dist⟩}•_while_(days⊸>⊑)0‿dist‿0‿0
}
