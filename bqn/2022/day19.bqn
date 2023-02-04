lib ← •Import "../lib.bqn"

Solve ⇐ { part 𝕊 line:
  "≢data" lib.Debug ≢data ← >{is ← lib.ParseInts 𝕩
    4‿3⥊∾⟨ 
       ⟨0, 0, 1⊑is⟩
       ⟨0, 0, 2⊑is⟩
       ⟨0, 3⊑is, 4⊑is⟩
       ⟨5⊑is, 0, 6⊑is⟩
    ⟩}¨ line
  "data[0‿0]" lib.Debug 0⊏0⊏data
  {
    1=part ?
        ⟨⟩
    ;
        ⟨⟩
  }
}
