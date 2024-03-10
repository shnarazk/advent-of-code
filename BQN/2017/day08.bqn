Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  Parse ← {s‿o‿x‿if‿t‿c‿y : ⟨s,"inc"≡o,util.ParseInt x,t,c,util.ParseInt y⟩}
  data (Parse" "⊸util.Split)¨ ↩
  vars ← ∧⍷⥊0‿3⊏⍉>data
  ops ← ∧⍷4⊸⊑¨data
  l ← ≠ data {ops⊸⊐⌾(4⊸⊏) 𝕩}∘{vars⊸⊐⌾(0‿3⊸⊏) 𝕩}¨ ↩
  state ← {pc‿regs‿max : ⟨dest,mode,inc,reg,kind,val⟩ ← pc⊑data
    {
      reg⊑regs (kind◶⟨≠,<,≤,=,>,≥⟩) val ?
      regs mode◶⟨-inc,inc⟩⊸+⌾(dest⊸⊑) ↩
      max (dest⊑regs)⊸⌈ ↩ ;
      @
    }
    ⟨1+pc,regs,max⟩
  }•_while_((0⊸≤∧l⊸>)⊑)⟨0,(≠vars)↑0,0⟩
  (2=part)◶⟨⌈´1⊸⊑,2⊸⊑⟩state
}
