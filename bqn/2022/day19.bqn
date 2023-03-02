lib‿⟨_to_heap⟩ ← •Import¨ "../lib.bqn"‿"../heap.bqn"
ore‿clay‿obsidian‿geode ← ↕4

Solve ⇐ { part 𝕊 line:
  "≢data" lib.Debug ≢data ← >{
    is ← lib.ParseInts 𝕩
    4‿4⥊⟨
          1⊑is,    0,    0,   0,
          2⊑is,    0,    0,   0,
          3⊑is, 4⊑is,    0,   0,
          5⊑is,    0, 6⊑is,   0,
        ⟩
  }¨ line
  {
    0=part ?
      state1 ← state ← 1‿0‿⟨5,14,3,0⟩‿⟨1,1,0,1⟩
      "blueprint" lib.Debug blueprint ← ⊏data
      "state" lib.Debug state
      "producible" lib.Debug {(𝕩⊏blueprint) (∧´≤) 2⊑state}¨↕4
      0
    ; 1=part ?
        limit ← 24
        Examine ← { 𝕊 n:
          max_so_far ← 0
          bp ← n⊏data
          robot_limits ← 3↑⌈´˘⍉bp
          state ← ⟨0⟩∾⟨0,0,0,0⟩∾⟨1,0,0,0⟩ # ⟨time,resources,robots⟩
          to_visit ← ⟨state⟩
          Expand ← { 𝕊 to_visit:
            new_states ← ⟨⟩
            { 𝕊 state:
              time ← -⊑state
              resources ← 4↑1↓state
              robots ← 5↓state
              max_so_far (geode⊑resources+(limit-time)×robots)⊸⌈ ↩
              { 𝕊 robot:
                mask ← 0< required ← robot⊏bp
                { ∧´mask/0<robots ?
                    req‿res‿rob ← (mask⊸/)¨required‿resources‿robots
                    t ← time+ wait ← 1+⌈⌈´rob÷˜req(0⊸⌈-)res
                    { t < limit ?
                        generated ← required-˜resources+wait×robots
                        robots_   ← (1⊸+)⌾(robot⊸⊑)robots
                        new_state ← (-t)∾generated∾robots_
                        # { 0<≠new_states ?
                        #     "state" lib.Debug new_state
                        #     "stack" lib.Debug new_states
                        #     lib.Debug¨ new_states
                        #     "check" lib.Debug ({𝕊 t‿s‿b: t∧(∧´s)∧(∧´b)}new_state⊸≤)¨new_states
                        #   ; @
                        # }
                        { (∨´(∧´new_state⊸≤)¨new_states)∨(∨´robot_limits<3↑robots_) ? @
                          ;
                            new_states ⟨new_state⟩⊸∾ ↩
                        }
                      ;@
                    }
                  ;@
                }
              }¨↕4
            }¨to_visit
            new_states
          }
          lib.While { 𝕤, 0<≠to_visit }‿{ 𝕤, to_visit Expand ↩ }
          "=" lib.Debug (n+1)×max_so_far
        }
        +´Examine¨↕≠data
    ; 2=part ?
        limit ← 32
        Examine ← { 𝕊 n:
          max_so_far ← 0
          bp ← n⊏data
          robot_limits ← 3↑⌈´˘⍉bp
          state ← ⟨0⟩∾⟨0,0,0,0⟩∾⟨1,0,0,0⟩ # ⟨time,resources,robots⟩
          to_visit ← ⟨state⟩
          Expand ← { 𝕊 to_visit:
            new_states ← ⟨⟩
            { 𝕊 state:
              time ← -⊑state
              resources ← 4↑1↓state
              robots ← 5↓state
              max_so_far (geode⊑resources+(limit-time)×robots)⊸⌈ ↩
              { 𝕊 robot:
                mask ← 0< required ← robot⊏bp
                { ∧´mask/0<robots ?
                    req‿res‿rob ← (mask⊸/)¨required‿resources‿robots
                    t ← time+ wait ← 1+⌈⌈´rob÷˜req(0⊸⌈-)res
                    { t < limit ?
                        generated ← required-˜resources+wait×robots
                        robots_   ← (1⊸+)⌾(robot⊸⊑)robots
                        new_state ← (-t)∾generated∾robots_
                        # { 0<≠new_states ?
                        #     "state" lib.Debug new_state
                        #     "stack" lib.Debug new_states
                        #     lib.Debug¨ new_states
                        #     "check" lib.Debug ({𝕊 t‿s‿b: t∧(∧´s)∧(∧´b)}new_state⊸≤)¨new_states
                        #   ; @
                        # }
                        { (∨´(∧´new_state⊸≤)¨new_states)∨(∨´robot_limits<3↑robots_) ? @
                          ;
                            new_states ⟨new_state⟩⊸∾ ↩
                        }
                      ;@
                    }
                  ;@
                }
              }¨↕4
            }¨to_visit
            new_states
          }
          lib.While { 𝕤, 0<≠to_visit }‿{ 𝕤, to_visit Expand ↩ }
          "=" lib.Debug max_so_far
        }
        ×´Examine¨↕3
    ;
        ⟨⟩
  }
}
