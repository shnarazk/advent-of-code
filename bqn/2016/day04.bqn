Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug 2↑data ↩ ("-[]"⊸util.Tokenize)¨data
  {
    1=part ?
      +´3⊸⊑¨(⊑≡2⊸⊑)¨⊸/<˘{s‿p‿c : ⟨1⊸⊑¨5↑∧((-/⁼∘⊐)⋈¨⍷)s,s,p,c⟩}˘>(¯2⊸(<∘∾∘↓∾((util.ParseInt∘⊣⋈˜⊢)´∘↑)))¨data
 ;
    0
  }
}
