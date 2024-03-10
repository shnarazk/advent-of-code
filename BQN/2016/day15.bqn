Solve ⇐ {env‿part 𝕊 data :
  math‿util ← •Import¨"/math.bqn"‿"/util.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInts¨ ↩
  # "data" util.Debug ⍉>data
  # "mod add" util.Debug (>{𝕨⋈𝕨|𝕩}˝)⌾(1‿3⊸⊏)(>{𝕨⋈𝕨+𝕩}˝)⌾(0‿3⊸⊏)⍉>data
  -´math.CRT´(2=part)◶⟨⊢,⟨⟨11,1+≠data⟩⟩⊸∾⟩<˘⍉1‿3⊏(>{𝕨⋈𝕨|𝕩}˝)⌾(1‿3⊸⊏)(>{𝕨⋈𝕨+𝕩}˝)⌾(0‿3⊸⊏)⍉>data
}
