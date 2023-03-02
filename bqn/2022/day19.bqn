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
    max_so_far   ← 0
    bp           ← n⊏data
    robot_limits ← 3↑⌈´˘⍉bp
    Expand ← {
      𝕊 ⟨⟩: max_so_far;
      𝕊 to_visit:
        new_states ← ⟨⟩
        { 𝕊 state:
          time‿resources‿robots ← ⟨-⊑state,4↑1↓state,5↓state⟩
          max_so_far (¯1⊑resources+(limit-time)×robots)⊸⌈ ↩
          { 𝕊 robot:
            mask ← 0< required ← robot⊏bp
            { ∧´mask/0<robots ?
                req‿res‿rob ← (mask⊸/)¨required‿resources‿robots
                time_ ← time+ wait ← 1+⌈⌈´rob÷˜req(0⊸⌈-)res
                { time_ < limit ?
                    resources_ ← required-˜resources+wait×robots
                    robots_    ← (1⊸+)⌾(robot⊸⊑)robots
                    state_     ← (-time_)∾resources_∾robots_
                    { (∧´robot_limits≥3↑robots_) ? ¬∨´(∧´state_⊸≤)¨new_states ? new_states ⟨state_⟩⊸∾ ↩ ;@ }
                  ;@
                }
              ;@
            }
          }¨↕4
        }¨to_visit
        𝕊 new_states
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
