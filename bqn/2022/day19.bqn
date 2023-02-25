lib‿⟨_to_heap⟩ ← •Import¨ "../lib.bqn"‿"../heap.bqn"
ore‿clay‿obsidian‿geode ← ↕4

# returns the goodness
Value ← { blueprint 𝕊 ·‿·‿resources‿robots: 0 {𝕨+2×𝕩}´ robots }
Producible ← ∧´{ (0=𝕨)∨(0<𝕩) }¨
RequiredResources ← (0⊸⌈-)
# FIXME: this is incorrect: count the number of robots
RequiredTime ← ⌈´∘(0⊸⌈-)

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
  # To_visit ← (>○(1⊸⊑))_to_heap
  # To_visit ← (>○(¯1⊸⊑))_to_heap
  # to_visit.Push "state" lib.Debug <state ← 1‿0‿⟨1,0,0,0⟩‿⟨1,0,0,0⟩  # heap of ⟨power,time,resources,robots⟩
  # visited ← ⟨state⟩
  {
    0=part ?
      state1 ← state ← 1‿0‿⟨5,14,3,0⟩‿⟨1,1,0,1⟩
      "blueprint" lib.Debug blueprint ← ⊏data
      "state" lib.Debug state
      "producible" lib.Debug {(𝕩⊏blueprint) (∧´≤) 2⊑state}¨↕4
      0
      ;
    1=part ?
        limit ← 24
        Examine ← { 𝕊 n:
          max_so_far ← 0
          bp ← n⊏data
          To_visit ← (>○⊑)_to_heap
          to_visit.Push <⟨⟩ lib.Debug state ← 0‿⟨1,0,0,0⟩‿⟨1,0,0,0⟩ # heap of ⟨time,resources,robots⟩
          Expand ← { 𝕊 time‿resources‿robots:
            { 𝕊 robot: 
              mask ← 0< required ← robot⊏bp
              { ∧´mask/0<robots ? 
                  req‿res‿rob ← (mask⊸/)¨required‿resources‿robots
                  wait ← ⌈⌈´rob÷˜req(0⊸⌈-)res
                  ! 0≤wait
                  t ← time+wait+1
                  { t < limit ?
                      generated ← required-˜resources+wait×robots
                      ⟨⟩ lib.Debug new_state ← t‿generated‿((1⊸+)⌾(robot⊸⊑)robots)
                      to_visit.Push < new_state
                    ;
                      max_so_far (¯1⊑resources+(limit-time)×robots)⊸⌈ ↩
                  }
                ;@
              }
            }¨ ↕4
          }
          lib.While { 𝕤, ¬to_visit.Empty @ }‿{ 𝕤, state ← to_visit.Pop @, Expand state }
          "=" lib.Debug (n+1) × max_so_far
        }
        ⌈´Examine¨↕≠data
    ;
        ⟨⟩
  }
}
