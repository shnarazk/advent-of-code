Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  width ← ⌈´≠¨¯1↓data
  map ← >width⊸↑¨¯2↓data
  unit_size ← map≠⊸÷4
  map ↩ ¯1⌽⎉2 ¯1⌽⎉1(2+≢map)↑map
  Warp ← {loc 𝕊 vec :
    ⟨¯1, 0⟩≡𝕩 ? (1⊑𝕨)∾˜¯1⊑1⊑⊔' '≠(1⊑𝕨)⊏⎉1 map ;
    ⟨ 1, 0⟩≡𝕩 ? (1⊑𝕨)∾˜  ⊑1⊑⊔' '≠(1⊑𝕨)⊏⎉1 map ;
    ⟨ 0,¯1⟩≡𝕩 ? ( ⊑𝕨)∾ ¯1⊑1⊑⊔' '≠( ⊑𝕨)⊏⎉2 map ;
    ⟨ 0, 1⟩≡𝕩 ? ( ⊑𝕨)∾   ⊑1⊑⊔' '≠( ⊑𝕨)⊏⎉2 map ;
    !0
  }
  "# path" util.Debug (20⌊≠)⊸↑path ← ∾⟜"→"¯1⊑data
  route ← ¯1⊸(util.ParseInt∘↓⋈{-¬⊑"L→R"⊸⊐𝕩}∘⊑)¨((0∾·<´¨·⥊·<˘2⊸↕)⊸(-˜)+`path∊"LR→")⊔path
  start ← 1∾⊑"."⊒˜1⊏map
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
  Move2 ← {dist‿turn 𝕊 loc‿dir :
    {
      '.'≡(n ← loc+dir⊑⟨¯1‿0,0‿1,1‿0,0‿¯1⟩)⊑map ? loc ↩ n ⋄ -¬𝕩 ;
      '#'≡(n ← loc+dir⊑⟨¯1‿0,0‿1,1‿0,0‿¯1⟩)⊑map ? 0 ;
      e ← unit_size-1
      loc1‿dir1 ← {
        patch ← 𝕩⌊∘÷unit_size
        dy‿dx ← unit_size|𝕩
        {
          # vertical warp
          ⟨0,1⟩‿0 : ⟨⟨dx,  0⟩+unit_size×3‿0,1⟩ ;
          ⟨0,2⟩‿0 : ⟨⟨e,  dx⟩+unit_size×3‿0,0⟩ ;
          ⟨0,2⟩‿2 : ⟨⟨dx,  e⟩+unit_size×1‿1,3⟩ ;
          ⟨2,0⟩‿0 : ⟨⟨dx,  0⟩+unit_size×1‿1,1⟩ ;
          ⟨2,1⟩‿2 : ⟨⟨dx,  e⟩+unit_size×3‿0,3⟩ ;
          ⟨3,0⟩‿2 : ⟨⟨0,  dx⟩+unit_size×0‿2,2⟩ ;
          # horizontal warp
          ⟨0,1⟩‿3 : ⟨⟨e-dy,0⟩+unit_size×2‿0,1⟩ ;
          ⟨0,2⟩‿1 : ⟨⟨e-dy,e⟩+unit_size×2‿1,3⟩ ;
          ⟨1,1⟩‿3 : ⟨⟨0,  dy⟩+unit_size×2‿0,2⟩ ;
          ⟨1,1⟩‿1 : ⟨⟨e,  dy⟩+unit_size×0‿2,0⟩ ;
          ⟨2,0⟩‿3 : ⟨⟨e-dy,0⟩+unit_size×0‿1,1⟩ ;
          ⟨2,1⟩‿1 : ⟨⟨e-dy,e⟩+unit_size×0‿2,3⟩ ;
          ⟨3,0⟩‿3 : ⟨⟨0,  dy⟩+unit_size×0‿1,2⟩ ;
          ⟨3,0⟩‿1 : ⟨⟨e,  dy⟩+unit_size×2‿1,0⟩ ;
          !0
        }patch‿dir
      }⌾(-¬)loc    # under the zero-indexed space
      count ← 𝕩
      {'.'≡loc1⊑map ? loc‿dir ↩ ⟨loc1,dir1-1⟩ ⋄ -¬count ; '#'≡loc1⊑map ? 0 ; !0}
    }•_while_(0⊸<)dist
    ⟨loc, 4|4+dir+turn⟩
  }
  {
    f ← {1=part ? Move ; Move2}
    {(y‿x)‿dir : (4|3+dir)+(4×x)+1000×y}start‿1 F´⌽route
  }
}
