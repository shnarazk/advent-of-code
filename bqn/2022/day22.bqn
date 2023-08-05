Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  width ← ⌈´≠¨¯1↓data
  "map size" util.Debug ≢map ← >width⊸↑¨¯1↓data
  "# path" util.Debug (20⌊≠)⊸↑path ← ∾⟜"→"¯1⊑data
  "# parse" util.Debug (+`path∊"LR→")
  "# group" util.Debug (0∾·<´¨·⥊·<˘2⊸↕)⊸(-˜)"# scan sum" util.Debug+`path∊"LR→"
  "route" util.Debug ¯1⊸(util.ParseInt∘↓⋈⊑)¨((0∾·<´¨·⥊·<˘2⊸↕)⊸(-˜)+`path∊"LR→")⊔path
  route ← ¯1⊸(util.ParseInt∘↓⋈{-¬⊑"L→R"⊸⊐𝕩}∘⊑)¨((0∾·<´¨·⥊·<˘2⊸↕)⊸(-˜)+`path∊"LR→")⊔path
  "start" util.Debug start ← 0∾⊑"."⊒˜1⊏map
  start‿1{dist‿turn 𝕊 loc‿dir : "step" util.Debug dist⋄ ⟨loc,4|dir+turn⟩}´⌽route
}
