Solve ⇐ {env‿part 𝕊 data :
  util‿⟨md5⟩ ← •Import¨"/util.bqn"‿"/md5.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ⊑ ↩
  !(Md5 "abcdef609043") util.StartsWith "00000"
  target ← (2=part)◶⟨"00000","000000"⟩@
  1⊑{(Md5(data∾•Fmt 1⊑𝕩)) util.StartsWith target ? 0∾1⊑𝕩 ; ⟨0,1⟩+𝕩} •_while_⊑1‿10000
}
