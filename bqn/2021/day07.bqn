Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜ "," env.Var⌾⋈ "BQN_LIB"
  min‿max ← (⌊´⋈⌈´) line ← util.ParseInt¨ "," util.Tokenize∾data
  {1=part ? ⌊´(+´line⊸(|∘-))¨min+↕max¬min ; ⌊´(+´line⊸((+´↕)¨1+|∘-))¨min+↕max¬min}
}
