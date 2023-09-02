Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  +´{1=part ? (+´·3‿2‿2⊸×·×´˘2⊸↕)¨∾⟜⊑∘∧¨𝕩 ; (×´+2⊸×∘(+´)∘(2⊸↑))¨∧¨𝕩}util.ParseInts¨data
}
