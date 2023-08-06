Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  width ← ⌈´≠¨¯1↓data
  "map size" util.Debug ≢map ← >width⊸↑¨¯2↓data
  "# map" util.Debug map
  unit_size ← map≠⊸÷4
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
  "# route" util.Debug ¯1⊸(util.ParseInt∘↓⋈⊑)¨((0∾·<´¨·⥊·<˘2⊸↕)⊸(-˜)+`path∊"LR→")⊔path
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
  # divide world into 6 patches
  # p01,p02,p11,p20,p21,p30
  # p00 ← ⍉p20
  # p10 ←
  Move2 ← {dist‿turn 𝕊 loc‿dir :
    {
      vec ← dir⊑⟨¯1‿0,0‿1,1‿0,0‿¯1⟩
      '.'≡(n ← vec+loc)⊑map ? loc ↩ n ⋄ -¬𝕩 ;
      vec ← dir⊑⟨¯1‿0,0‿1,1‿0,0‿¯1⟩
      '#'≡(n ← vec+loc)⊑map ? 0 ;
      patch ← (¯1+loc)⌊∘÷unit_size
      dy‿dx ← unit_size|¯1+loc # back to zero-indexed space
      # patch_no.‿dir → worp target positioni
      e ← unit_size-1
      o ← ⟨1,1⟩
      newloc‿newdir ← {
        # vertical warp
        ⟨0,1⟩‿0 : ⟨o+⟨dx,  0⟩+unit_size×3‿0,1⟩ ;
        ⟨0,2⟩‿0 : ⟨o+⟨0,  dx⟩+unit_size×3‿0,0⟩ ;
        ⟨0,2⟩‿2 : ⟨o+⟨dx,  e⟩+unit_size×1‿1,3⟩ ;
        ⟨2,0⟩‿0 : ⟨o+⟨dx,  0⟩+unit_size×1‿1,1⟩ ;
        ⟨2,1⟩‿2 : ⟨o+⟨dx,  e⟩+unit_size×3‿0,3⟩ ;
        ⟨3,0⟩‿2 : ⟨o+⟨dx,  0⟩+unit_size×0‿2,2⟩ ;
        # horizontal warp
        ⟨0,1⟩‿3 : ⟨o+⟨e-dy,0⟩+unit_size×2‿0,1⟩ ;
        ⟨0,2⟩‿1 : ⟨o+⟨e-dy,0⟩+unit_size×2‿1,3⟩ ;
        ⟨1,1⟩‿3 : ⟨o+⟨0,  dy⟩+unit_size×2‿0,2⟩ ;
        ⟨1,1⟩‿1 : ⟨o+⟨e,  dy⟩+unit_size×0‿2,0⟩ ;
        ⟨2,0⟩‿3 : ⟨o+⟨e-dy,0⟩+unit_size×0‿1,1⟩ ;
        ⟨2,1⟩‿1 : ⟨o+⟨e-dy,e⟩+unit_size×0‿2,3⟩ ;
        ⟨3,0⟩‿3 : ⟨o+⟨0,  dy⟩+unit_size×0‿1,2⟩ ;
        ⟨3,0⟩‿1 : ⟨o+⟨e,  dy⟩+unit_size×2‿1,0⟩ ;
        (𝕩⋈loc)!0
      }patch‿dir
      count ← 𝕩
      "newloc" util.Debug newloc
      {'.'≡newloc⊑map ? loc‿dir ↩ newloc‿newdir ⋄ -¬count ; '#'≡newloc⊑map ? 0 ; !0}
    }•_while_(0⊸<)dist
    ⟨loc, 4|4+dir+turn⟩
  }
  {
    1=part ? {(y‿x)‿dir : "goal" util.Debug 𝕩 ⋄ (4|3+dir)+(4×x)+1000×y}start‿1 Move´⌽route ;
    {(y‿x)‿dir : "goal" util.Debug 𝕩 ⋄ (4|3+dir)+(4×x)+1000×y}start‿1 Move2´⌽route
  }
}
