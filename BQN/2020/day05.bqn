Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ >˘7(↑⋈↓)¨('B'⊸=∨'R'⊸=)¨data
  {1=part ? ⌈´8⊸×⊸+´˘{𝕨+2×𝕩}´∘⌽¨data ; ⊑(127⊸≤)⊸/1+⊑¨(¯2=-´)¨⊸/<˘2↕∧8⊸×⊸+´˘{𝕨+2×𝕩}´∘⌽¨data}
}
