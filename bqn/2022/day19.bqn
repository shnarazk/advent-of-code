lib‿⟨_to_heap⟩ ← •Import¨ "../lib.bqn"‿"../heap.bqn"
ore‿clay‿obsidian‿geode ← ↕4

# returns the goodness (mining ability)
Value ← { blueprint 𝕊 ·‿·‿resources‿robots:
  k0‿k1‿k2‿k3 ← ⊑⟜blueprint(∾⟜0)¨↕4
  k2 (k1×2‿1⊑blueprint)⊸+ ↩
  k3 (k2×3‿2⊑blueprint)⊸+ ↩
  (geode⊑resources)++´k0‿k1‿k2‿k3×robots
}

Solve ⇐ { part 𝕊 line:
  "≢data" lib.Debug ≢data ← >{
    is ← lib.ParseInts 𝕩
    4‿4⥊⟨0,    0,    0, 1⊑is,
         0,    0,    0, 2⊑is,
         0,    0, 3⊑is, 4⊑is,
         0, 5⊑is,    0, 6⊑is⟩
  }¨ line
  "data[0‿0]" lib.Debug 0⊏0⊏data
  {
    1=part ?
        To_visit ← (>○(¯1⊸⊑))_to_heap
        to_visit.Push<state ← 1‿0‿⟨0,0,0,1⟩‿⟨0,0,0,1⟩  # heap of ⟨power,time,resources,robots⟩
        visited ← ⟨state⟩
        max_so_far ← 0
        Expand ← { bp 𝕊 power‿time‿resources‿robots:
          geodes ← 0
          { max_so_far<geodes ? max_so_far ↩ geodes ; @ }
          {𝕊 robot:
            required ← robot⊏bp
            { required ∧´< resources ?
                 new_state ← state
                 to_visit.Push < new_state
              ;@
            }
          } ↕3
        }
        bp ← ⊑data
        lib.While { 𝕤, ¬to_visit.Empty @ }‿{ 𝕤, state ← to_visit.Pop @, bp Expand state }
        ⟨⟩
    ;
        ⟨⟩
  }
}
