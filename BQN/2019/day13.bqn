Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  intcode ← •Import "/2019/intcode.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  data util.ParseInts∘⊑ ↩
  shape ← ⋈˜´1+2↑⊏∨output←∘‿3⥊((intcode.Intcode data).Run@).Output@
  {
    1=part ? +´2=⥊¯1⊑˘∘‿3⥊((intcode.Intcode data).Run@).Output@ ;
    breakout ← 0 (intcode.Intcode data).Set 2
    score ← 0
    screen ← 0¨↕shape
    {
      s ← (⟨⟩⊸≢)◶⟨¯∞,2⊸⊑⊑⟩⊑output ← (¯1‿0≢(2⊸↑))¨⊸⊔ <˘∘‿3⊸⥊(𝕩.Run@).Output@
      {¯∞≠s ? score ↩ s ; @}
      paddle ← (⟨⟩⊸≢)◶⟨0‿0,⌽2↑⊑⟩(3≡2⊸⊑)¨⊸/1⊑output
      ball ← (⟨⟩⊸≢)◶⟨0‿0,⌽2↑⊑⟩(4≡2⊸⊑)¨⊸/1⊑output
      {x‿y‿c : screen c⌾(y‿x⊸⊑) ↩}¨1⊑output
      util.Progress(⊑⟜" #*-○")¨screen
      𝕩.Input⟨ball×∘-○(1⊸⊑)paddle⟩
    }•_while_{𝕤 ⋄ intcode.halt≠𝕩.Status@}breakout
    "final scene" util.Debug (⊑⟜" #*-○")¨screen
    score
  }
}
