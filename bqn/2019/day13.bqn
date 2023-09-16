Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  intcode ← •Import "/2019/intcode.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  data util.ParseInts∘⊑ ↩
  {
    1=part ? +´2=⥊¯1⊑˘∘‿3⥊((intcode.Intcode data).Run@).Output@ ;
    shape ← ⋈˜´1+2↑⊏∨output←∘‿3⥊((intcode.Intcode data).Run@).Output@
    ⊑⟜" #*-○"¨shape⥊¯1⊑˘output
  }
}
