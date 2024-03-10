Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  nodes ← ∧⍷∾⥊ adj ← ⍉≍⌽¨⊸∾"-"⊸util.Split¨data
  ends ← s‿e ← -nodes⊐"start"‿"end"
  map ← (+´'Z'⊸≥∘⊑¨nodes)⊸≤◶⟨⊢,-⟩¨∘∧¨1⊸⊑¨¨⊑¨⊸⊔nodes⊸⊐¨adj
  check ← {1=part ? {¬∘⊑𝕩∊𝕨} ; {((1≥(+´1⊸=))∧(∧´1⊸≥))∘⊒·0⊸>⊸/𝕩∾𝕨}}
  c ← 0
  ∾∘({(⊑(⊑𝕩)∊ends)∧1<≠𝕩 ? c (e=⊑𝕩)⊸+ ↩ ⋄ ⟨⟩ ; ∾⟜𝕩˜¨0⊸>◶⟨1,𝕩⊸Check⟩¨⊸/map⊑˜|⊑𝕩}¨)•_while_(⟨⟩⊸≢)⋈⋈s
  c
}
