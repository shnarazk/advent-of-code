Solve ⇐ {env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data '#'⊸=∘> ↩
  Embed ← {s ← ≢𝕩 ⋄  ¯10⌽⎉1 ¯10⌽(20+s)↑𝕩}
  data ↩ Embed data
  h‿w ← ≢data
  Avls ← {map‿r 𝕊 y‿x :
    {
      (0=y)∨(0=x)∨(y=h)∨(x=w) ? 4↑0 ;
      1≥+´({y‿x : (0≤y)∧(0≤x)∧(y<h)∧(x<w)}¨⊸/⥊y‿x⊸+¨¯1+↕3‿3)⊑map ? 4↑0 ;
      avN ← {(1<y)∧(1≤x)∧(x≤w) ? ¬⟨y-1,x-1⟩⊑map ? ¬⟨y-1,x  ⟩⊑map ? ¬⟨y-1,x+1⟩⊑map ? ⟨y,x⟩⊑map ; 0}
      avS ← {(h>y)∧(1≤x)∧(x≤w) ? ¬⟨y+1,x-1⟩⊑map ? ¬⟨y+1,x  ⟩⊑map ? ¬⟨y+1,x+1⟩⊑map ? ⟨y,x⟩⊑map ; 0}
      avW ← {(1≤y)∧(y≤h)∧(1<x) ? ¬⟨y-1,x-1⟩⊑map ? ¬⟨y  ,x-1⟩⊑map ? ¬⟨y+1,x-1⟩⊑map ? ⟨y,x⟩⊑map ; 0}
      avE ← {(1≤y)∧(y≤h)∧(w>x) ? ¬⟨y-1,x+1⟩⊑map ? ¬⟨y  ,x+1⟩⊑map ? ¬⟨y+1,x+1⟩⊑map ? ⟨y,x⟩⊑map ; 0}
      (r-1)⌽⟨avN,avS,avW,avE⟩
    }
  }
  Moves ← {map‿r 𝕊 𝕩 :
    ToN ← {y‿x : ⟨y-1,  x⟩} # ⋄ !0‿0  ≡ ToN 1‿0
    ToS ← {y‿x : ⟨y+1,  x⟩} # ⋄ !2‿0  ≡ ToS 1‿0
    ToW ← {y‿x : ⟨  y,x-1⟩} # ⋄ !0‿1  ≡ ToW 0‿2
    ToE ← {y‿x : ⟨  y,x+1⟩} # ⋄ !1‿10 ≡ ToE 1‿9
    (r-1)⌽⟨ToN 𝕩,ToS 𝕩,ToW 𝕩,ToE 𝕩⟩
  }
  Locations ← {map‿r 𝕊 pos : map‿r(Avls/Moves)pos} # at most 4 cands
  NextLocation ← (¬∘≠⊸↓)∘Locations                 # at most 1 location
  CountGround ← {𝕊 m :                             # sum of empty cells
    area ← ×´(¬´¯1‿0⊏∧)˘⍉>alive ← ⊑⟜m¨⊸/⥊↕≢m
    area-≠alive
  }
  {
    1=part ?
      CountGround 1⊑{step‿data :
        0 lib.Progress "↑1. Make destination map"
        0 lib.Progress destination ← {data‿(4|step) NextLocation 𝕩}¨↕≢data
        0 lib.Progress "→2. Aggregate congestion map by using a tricky 0→1→∞ counter"
        0 lib.Progress congestion ← (data≢⊸↑0){𝕨𝕊𝕩 : (÷0⊸=)⌾(𝕨⊸⊑)𝕩}´⥊>⟨⟩⊸≢¨⊸/⥊destination
        0 lib.Progress "↓3. Collapse elements by (1=≠)"
        0 lib.Progress moved ← 1=congestion
        0 lib.Progress "←4. Erase Elves from data if ¬destination⊑congestion"
        remain ← {p ← 𝕩⊑destination ⋄  ⟨⟩≢p ? ¬p⊑⊸⊑moved ; 𝕩⊑data}¨↕≢data
        0 lib.Progress " 5. update 𝕩 with the combined map"
        # {10=step ? ∞ ; 0.1} lib.Progress remain∨moved
        ⟨1+step, remain∨moved⟩
      }•_while_(10≥⊑) 1‿data ;
    2=part ? 0
  }
}
