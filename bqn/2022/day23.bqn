Solve ⇐ {env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data '#'⊸=∘> ↩
  maxY‿maxX ← ≢data
  "" lib.Debug ⊏data
  Avls ← {0𝕊𝕩 ;
    AvN ← {y‿x :      0<y} ⋄ !¬AvN 0‿0
    AvS ← {y‿x : maxY>1+y} ⋄ !¬AvS (maxY-1)‿0
    AvW ← {y‿x :      0<x} ⋄ !¬AvW 0‿0
    AvE ← {y‿x : maxX>1+x} ⋄ !¬AvE 0‿(maxX-1)
    𝕨⌽⟨AvN 𝕩,AvS 𝕩,AvW 𝕩,AvE 𝕩⟩
  }
  "" lib.Debug Avls 0‿0
  Moves ← {0𝕊𝕩 ;
    ToN ← {y‿x : ⟨y-1,  x⟩} ⋄ !0‿0 ≡ ToN 1‿0
    ToS ← {y‿x : ⟨y+1,  x⟩} ⋄ !2‿0 ≡ ToS 1‿0
    ToW ← {y‿x : ⟨  y,x-1⟩} ⋄ !0‿1 ≡ ToW 0‿2
    ToE ← {y‿x : ⟨  y,x+1⟩} ⋄ !1‿10 ≡ ToE 1‿9
    𝕨⌽⟨ToN 𝕩,ToS 𝕩,ToW 𝕩,ToE 𝕩⟩
  }
  Locations ← {map‿r 𝕊 pos : (⊑⟜map)¨⊸/r(Avls/Moves)pos} # at most 4 cands
  NextLocation ← ¬∘≠⊸↓Locations                          # at most 1 location
  CountGround ← {<⁼+˝+˝¬𝕩}                               # sum of empty cells
  {
    1=part ?
      CountGround 1⊑{step‿data :
        # data ¬¨ ↩
        lib.Progress{≠data‿(4|step) NextLocation 𝕩}¨↕≢data
        # Plan
        # 1. aggregate destination map,
        # 2. then agregate congestion map
        # 3. collapse elements by (1=≠)
        # 4. filter Elf if ¬destination⊑congestion, then add it to congestion map
        # 5. update 𝕩 with it
        k ← 10⊸↑˘10↑data
        # lib.Progress •Fmt k
        •Delay 0.8
        ⟨1+step, data⟩
      }•_while_(10>⊑) 0‿data ;
    2=part ? 0
  }
}
