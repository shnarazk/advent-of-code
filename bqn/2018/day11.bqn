Solve ⇐ {env‿part 𝕊 data :
  util‿geo ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⊑ ↩
  Power ← {y‿x:
    rackID ← x+10
    5-˜⌊100÷˜1000|rackID×data+y×rackID
  }
  p ← Power¨1+ shape ← ⋈⌜˜↕300
  {
    1=part ?
      stencil ← 300‿300↑1¨3‿3↑0
      1⊑⊑∨⥊{⟨1+𝕩,1+𝕨⟩⋈˜+´⥊p×(-𝕨‿𝕩)geo.Rotate stencil}⌜˜↕300-3
    ;
      1⊑1⊑{k‿x :
        util.Progress k∾x
        stencil ← 300‿300↑1¨k‿k↑0
        util.Progress(k+1)⋈⊑∨⟨x⟩∾⥊{⟨1+𝕩,1+𝕨,k⟩⋈˜+´⥊p×(-𝕨‿𝕩)geo.Rotate stencil}⌜˜↕300-k
        }•_while_(¯1⊸+⊸≤⟜(2×·2⊸⊑1⊸⊑)´)0‿⟨0,0‿0‿0⟩
  }
}
