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
  Examine ← { limit 𝕊 n:
    max_so_far ← 0
    bp         ← n⊏data
    masks      ← 0<˘ bp
    limits     ← 0‿0‿0‿∞⌈⌈´˘⍉bp
    Expand ← {
      𝕊 ⟨⟩: max_so_far;
      𝕊 to_visit:
        next ← ⟨⟩
        { 𝕊 state:
          time‿resources‿robots ← ⟨-⊑state,4↑1↓state,5↓state⟩
          max_so_far (¯1⊑resources+(limit-time)×robots)⊸⌈ ↩
          # FIXME: this is not an array oriented approach.
          { 𝕊 i:
            mask ← i⊏masks
            { ∧´0<mask/robots ?
                need ← i⊏bp
                ti   ← time+ wait ← 1+⌈⌈´(mask⊸/)robots÷˜need(0⊸⌈-)resources
                { ti < limit ?
                    res ← need-˜resources+wait×robots
                    rob ← (1⊸+)⌾(i⊸⊑)robots
                    s   ← (-ti)∾res∾rob
                    { (∧´rob≤limits) ? ¬∨´(∧´s⊸≤)¨next ? next ⟨s⟩⊸∾ ↩ ;@ }
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
