Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  intcode ← •Import "/2019/intcode.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  cheatsheat ← util.ParseInts⊑•file.Lines "/src/y2019/day13-joystick.rs"∾˜"." env.Var⌾⋈ "AOC_REPO_DIR"
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
      {x‿y‿c : screen c⌾(y‿x⊸⊑) ↩}¨1⊑output
      (÷10000)util.Progress(⊑⟜" #*-○")¨screen
      ⟨i⟩‿o ← 1(↑⋈↓)cheatsheat
      cheatsheat ↩ o
      𝕩.Input⟨i⟩
    }•_while_{𝕤 ⋄ intcode.halt≠𝕩.Status@}breakout
    "final scene" util.Debug (⊑⟜" #*-○")¨screen
    score
  }
}
