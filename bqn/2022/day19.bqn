lib‿⟨_to_heap⟩ ← •Import¨ "../lib.bqn"‿"../heap.bqn"
ore‿clay‿obsidian‿geode ← ↕4

# returns the goodness
Value ← { blueprint 𝕊 ·‿·‿resources‿robots: 0 {𝕨+2×𝕩}´ robots }

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
  To_visit ← (>○(¯1⊸⊑))_to_heap
  to_visit.Push<state ← 1‿0‿⟨1,0,0,0⟩‿⟨1,0,0,0⟩  # heap of ⟨power,time,resources,robots⟩
  visited ← ⟨state⟩
  {
    0=part ?
      state1 ← state ← 1‿0‿⟨5,14,3,0⟩‿⟨1,1,0,1⟩
      "blueprint" lib.Debug blueprint ← ⊏data
      "state" lib.Debug state
      "producible" lib.Debug {(𝕩⊏blueprint) (∧´≤) 2⊑state}¨↕4
      0
      ;
    1=part ?
        max_so_far ← 0
        Expand ← { bp 𝕊 power‿time‿resources‿robots:
          geodes ← 0
          { max_so_far<geodes  ? max_so_far ↩ geodes ; @ }
          { 𝕊 robot:
            "required" lib.Debug required ← robot⊏bp
            "resources" lib.Debug resources
            { required (∧´≤) resources ?
                 lib.Debug "passed"
                 new_state ← state
                 to_visit.Push < new_state
              ;@
            }
          }¨ ↕3
        }
        "bp" lib.Debug bp ← ⊏data
        lib.While { 𝕤, ¬to_visit.Empty @ }‿{ 𝕤, state ← to_visit.Pop @, bp Expand state }
        "_visited" lib.Debug visited
        ⟨⟩
    ;
        ⟨⟩
  }
}
