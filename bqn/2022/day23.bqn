Solve ⇐ {env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data '#'⊸=∘> ↩
  maxY‿maxX ← ≢data
  "" lib.Debug ⊏data
  Avls ← {0𝕊𝕩 ;
    AvN ← {y‿x :    0<y} ⋄ !¬AvN 0‿0
    AvS ← {y‿x : maxY>y} ⋄ !¬AvS 9‿0
    AvW ← {y‿x :    0<x} ⋄ !¬AvW 0‿0
    AvE ← {y‿x : maxX>x} ⋄ !¬AvE 0‿9
    𝕨⌽⟨AvN 𝕩,AvS 𝕩,AvW 𝕩,AvE 𝕩⟩
  }
  "" lib.Debug Avls 0‿0
  Moves ← {
    ToN ← {y‿x : ⟨y-1,  x⟩} ⋄ !0‿0 ≡ ToN 1‿0
    ToS ← {y‿x : ⟨y+1,  x⟩} ⋄ !2‿0 ≡ ToS 1‿0
    ToW ← {y‿x : ⟨  y,x-1⟩} ⋄ !0‿1 ≡ ToW 0‿2
    ToE ← {y‿x : ⟨  y,x+1⟩} ⋄ !1‿10 ≡ ToE 1‿9
    𝕨⌽⟨ToN 𝕩,ToS 𝕩,ToW 𝕩,ToE 𝕩⟩
  }
  Locations ← {map 𝕊 r‿pos : r⌽⊑⊸map⊸/(Avls/Moves)pos}
  CountGround ← {<⁼+˝+˝𝕩}
  {
    1=part ?
      CountGround 1⊑{step‿data :
        data ¬¨ ↩
        k ← 10⊸↑˘10↑data
        lib.Progress •Fmt k
        •Delay 0.1
        ⟨1+step, data⟩
      }•_while_(10>⊑) 0‿data ;
    2=part ? 0
  }
}
