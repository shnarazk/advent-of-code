Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  initial‿rules ← 2(↑⋈↓)data
  rules '#'⊸=¨¨∘(" => "⊸util.Split)¨ ↩
  rules (⊑¨(⟨1⟩≡1⊸⊑)¨⊸/) ↩ # pick up only generators
  initial '#'⊸=∘(15⊸↓)∘⊑ ↩
  grow ← 4
  Extend ← (grow↑0)⊸{𝕨∾𝕩∾𝕨}
  {
    1=part ?
      generation ← 20
      +´×⟜(-⟜(generation×grow÷2)∘↕≠)(rules∊˜(<˘5⊸↕∘Extend))⍟generation initial
      ;
    0
  }
}
