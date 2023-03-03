lib ← •Import "../lib.bqn"

Solve ⇐ { part 𝕊 line:
  data ← >{
    is ← lib.ParseInts 𝕩
    4‿4⥊⟨
          1⊑is,    0,    0,   0,
          2⊑is,    0,    0,   0,
          3⊑is, 4⊑is,    0,   0,
          5⊑is,    0, 6⊑is,   0,
        ⟩
  }¨ line
  Examine ← { u 𝕊 n:
    best‿bp‿upto ← ⟨0,n⊏data,-u⟩
    masks‿limits ← ⟨0<˘bp,0‿0‿0‿∞⌈⌈´˘⍉bp⟩
    Expand ← {
      𝕊 ⟨⟩: best;
      𝕊 to_visit:
        next ← ⟨⟩
        { 𝕊 state:
          time‿resources‿robots ← ⟨⊑state,4↑1↓state,5↓state⟩
          best (¯1⊑resources+(time-upto)×robots)⊸⌈ ↩
          { 𝕊 i:        # FIXME: this is not an array oriented approach.
            { robots≤○(i⊸⊑)limits ?
                need ← i⊏bp
                masked ← (i⊏masks)/robots÷˜need(0⊸⌈-)resources
                { upto< ti ← time- wait ← 1+⌈⌈´masked ?
                    s ← ti∾(need-˜resources+wait×robots)∾((1⊸+)⌾(i⊸⊑)robots)
                    { ¬∨´(∧´s⊸≤)¨next ? next ⟨s⟩⊸∾ ↩ ;@ }
                  ;@
                }
                ;@
              }
            }¨↕4
        }¨to_visit
        𝕊 next
    }
    (•Fmt n) lib.Debug Expand ⟨⟨0⟩∾⟨0,0,0,0⟩∾⟨1,0,0,0⟩⟩ # ⟨time,resources,robots⟩
  }
  {
    0=part   ? "≢data" lib.Debug ≢data
    ; 1=part ? +´ 24 ((1⊸+)×Examine)¨↕≠data
    ; 2=part ? ×´ 32 Examine¨↕3
    ; ⟨⟩
  }
}
