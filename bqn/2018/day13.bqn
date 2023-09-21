Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  dir ← ⟨¯1‿0,0‿¯1,0‿1,1‿0⟩
  symbol ← " /-\|+^<>v"
  data > ↩
  data symbol⊸⊐⌾⋈¨ ↩
  Clash ← ≠○≠⟜⍷1⊸⊑¨
  Next ← {
    d ← ⊏⟜dir-⟜6 os ← ⊑¨𝕩
    newpos ← d⊸+⌾(1⊸⊑¨)𝕩
    # FIXME
    >⍉d≍newpos
    𝕩∾𝕩
  }
  {
    1=part ?
      orientation ← ⊑dir
      locations ← ∾{𝕩⊸⋈¨(𝕩=⊑⟜data)¨⊸/⥊↕≢data}¨6+↕4
      ∧1⊸⊑¨locations
      3↑terminal ← Next•_while_(¬Clash)locations
    ;
    0
  }
}
