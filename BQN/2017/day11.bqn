Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  Dir ← ⟨1‿0,0‿1,1‿1,¯1‿¯1,0‿¯1,¯1‿0⟩⊑˜"nw"‿"ne"‿"n"‿"s"‿"sw"‿"se"⊸⊐⌾⋈
  (2=part)◶⟨(=○×´◶⟨+´|,⌈○|´⟩+´),(⌈´·(=○×´◶⟨+´|,⌈○|´⟩¨)+`)⟩Dir¨"," util.Split⊑data
}
