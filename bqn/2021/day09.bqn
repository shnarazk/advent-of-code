Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜ "," env.Var⌾⋈ "BQN_LIB"
  "map" util.Debug map ← (1⊸⌽∞⊸»⍟2)⎉1{𝔽 _𝕣 𝕩 : 𝔽⌾⍉𝔽 𝕩}(2+≢)⊸↑util.ParseInt∘⋈¨>data
  0
}
