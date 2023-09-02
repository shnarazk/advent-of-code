Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data (⟨¯1‿0,0‿1,1‿0,0‿¯1⟩⊸(⊑˜)¨ "^>v<"⊐⊑) ↩
  h ← 0‿0 Hashmap○⋈ part
  {
    1=part ? 0‿0{dy‿dx 𝕊 y‿x : pos ← dy‿dx+y‿x ⋄ pos h.Set 1+0 h.Get pos ⋄ pos}´⌽data ;
    (0‿0{dy‿dx 𝕊 y‿x : pos ← dy‿dx+y‿x ⋄ pos h.Set 1+0 h.Get pos ⋄ pos}´⌽)˘⍉∘‿2⥊data
  }
  ≠h.Values@
}
