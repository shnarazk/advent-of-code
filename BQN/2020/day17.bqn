Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashset⟩ ← •Import¨"/util.bqn"‿"/hashset.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  shape ←≢data (>'#'⊸=) ↩
  # "init map" util.Debug map.Values⁼@
  {
    1=part ?
      map ← Hashset 0⊸∾¨(⊑⟜data)¨⊸/⥊↕shape
      kernel ← ⟨0,0,0⟩⊸≢¨⊸/∧⥊(⊢∾⌜(⋈⌜˜))¯1+↕3
      Neighbors ← kernel+<
      Next ← {𝕊 map :
        next ← Hashset⟨⟩
        "# lives" util.Debug lives ← ¯1‿1+(⌊´⋈⌈´) map.Values⁼˜@
        "# targets" util.Debug targets ← ∧⥊(<⊑lives)+↕¬˜´lives
        Around ← +´(map.Has¨)∘Neighbors
        Alive ← map.Has◶⟨3=Around,∊⟜2‿3⌾⋈ Around⟩
        # Check ← Around
        # "check" util.Debug Check¨targets
        next.Set¨ Alive¨⊸/targets
        # (map.Count@) util.Debug next.Count@
        next
      }
      final ← Next⍟6 map
      final.Count@
    ;
      map ← Hashset 0‿0⊸∾¨(⊑⟜data)¨⊸/⥊↕shape
      util.Debug kernel ← ⟨0,0,0,0⟩⊸≢¨⊸/∧⥊(∾⌜˜(⋈⌜˜))¯1+↕3
      Neighbors ← kernel+<
      Next ← {𝕊 map :
        next ← Hashset⟨⟩
        "# lives" util.Debug lives ← ¯1‿1+(⌊´⋈⌈´) map.Values⁼˜@
        "# targets" util.Debug targets ← ∧⥊(<⊑lives)+↕¬˜´lives
        Around ← +´(map.Has¨)∘Neighbors
        Alive ← map.Has◶⟨3=Around,∊⟜2‿3⌾⋈ Around⟩
        # Check ← Around
        # "check" util.Debug Check¨targets
        next.Set¨ Alive¨⊸/targets
        # (map.Count@) util.Debug next.Count@
        next
      }
      final ← Next⍟6 map
      final.Count@

  }
}
