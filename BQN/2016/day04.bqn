Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ ("-[]"⊸util.Split)¨data
  {
    1=part ? +´3⊸⊑¨(⊑≡2⊸⊑)¨⊸/<˘{s‿p‿c : ⟨1⊸⊑¨5↑∧((-/⁼∘⊐)⋈¨⍷)s,s,p,c⟩}˘>(¯2⊸(<∘∾∘↓∾((util.ParseInt∘⊣⋈˜⊢)´∘↑)))¨data ;
    !<⁼"northpole"<⊸∊∧⍷∾⊑¨<˘{s‿p‿i : ⟨" "util.Split{'-'=𝕩 ? ' ' ; (26⊸|i⊸+)⌾(-⟜'a')𝕩}¨s,i⟩}˘>(¯2⊸(<∘(¯1↓∾)∘(∾⟜'-'¨)∘↓∾((util.ParseInt∘⊣⋈˜⊢)´∘↑)))¨data
    1⊑⊑(<⁼(<"northpole")∊⊑)¨⊸/⥊<˘{s‿p‿i : ⟨" "util.Split{'-'=𝕩 ? ' ' ; (26⊸|i⊸+)⌾(-⟜'a')𝕩}¨s,i⟩}˘>(¯2⊸(<∘(¯1↓∾)∘(∾⟜'-'¨)∘↓∾((util.ParseInt∘⊣⋈˜⊢)´∘↑)))¨data
  }
}
