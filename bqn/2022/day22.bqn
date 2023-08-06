Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  width ← ⌈´≠¨¯1↓data
  "map size" util.Debug ≢map ← >width⊸↑¨¯1↓data
  "map" util.Debug map
  map ↩ ¯1⌽⎉2 ¯1⌽⎉1(2+≢map)↑map
  "# horizontal slice 0" util.Debug ⊏⎉2 map
  "# horizontal slice 1" util.Debug 1⊏⎉2 map
  "# vertical slice 0" util.Debug ⊏⎉1 map
  "# vertical slice 2" util.Debug 2⊏⎉1 map
  Warp ← {loc 𝕊 vec :
    ⟨¯1, 0⟩≡𝕩 ? (1⊑𝕨)∾˜¯1⊑1⊑⊔' '≠(1⊑𝕨)⊏⎉1 map ;
    ⟨ 1, 0⟩≡𝕩 ? (1⊑𝕨)∾˜  ⊑1⊑⊔' '≠(1⊑𝕨)⊏⎉1 map ;
    ⟨ 0,¯1⟩≡𝕩 ? ( ⊑𝕨)∾ ¯1⊑1⊑⊔' '≠( ⊑𝕨)⊏⎉2 map ;
    ⟨ 0, 1⟩≡𝕩 ? ( ⊑𝕨)∾   ⊑1⊑⊔' '≠( ⊑𝕨)⊏⎉2 map ;
    !0
  }
  "# path" util.Debug (20⌊≠)⊸↑path ← ∾⟜"→"¯1⊑data
  "# parse" util.Debug (+`path∊"LR→")
  "# group" util.Debug (0∾·<´¨·⥊·<˘2⊸↕)⊸(-˜)"# scan sum" util.Debug+`path∊"LR→"
  "route" util.Debug ¯1⊸(util.ParseInt∘↓⋈⊑)¨((0∾·<´¨·⥊·<˘2⊸↕)⊸(-˜)+`path∊"LR→")⊔path
  route ← ¯1⊸(util.ParseInt∘↓⋈{-¬⊑"L→R"⊸⊐𝕩}∘⊑)¨((0∾·<´¨·⥊·<˘2⊸↕)⊸(-˜)+`path∊"LR→")⊔path
  "start" util.Debug start ← 1∾⊑"."⊒˜1⊏map
  Move ← {dist‿turn 𝕊 loc‿dir :
    vec ← dir⊑⟨¯1‿0,0‿1,1‿0,0‿¯1⟩
    {
      '.'≡(n ← vec+loc)⊑map ? loc ↩ n⋄ -¬𝕩 ;
      '#'≡(n ← vec+loc)⊑map ? 0 ;
      newloc ← loc Warp vec
      count ← 𝕩
      {'.'≡newloc⊑map ? loc ↩ newloc ⋄ -¬count ; '#'≡newloc⊑map ? 0 ; !0}
    }•_while_(0⊸<)dist
    ⟨loc, 4|4+dir+turn⟩
  }
  {(y‿x)‿dir : "goal" util.Debug 𝕩 ⋄ (4|3+dir)+(4×x)+1000×y}start‿1 Move´⌽route
}
