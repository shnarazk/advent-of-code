Solve ⇐ {env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ⟨HashMap⟩‿⟨HashSet⟩ ← •Import¨"/hashmap.bqn"‿"/hashset.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data '#'⊸=∘> ↩
  Moves ← {map‿r 𝕊 𝕩 :
    ToN ← {y‿x : ⟨y-1,  x⟩} # ⋄ !0‿0  ≡ ToN 1‿0
    ToS ← {y‿x : ⟨y+1,  x⟩} # ⋄ !2‿0  ≡ ToS 1‿0
    ToW ← {y‿x : ⟨  y,x-1⟩} # ⋄ !0‿1  ≡ ToW 0‿2
    ToE ← {y‿x : ⟨  y,x+1⟩} # ⋄ !1‿10 ≡ ToE 1‿9
    (r-1)⌽⟨ToN 𝕩,ToS 𝕩,ToW 𝕩,ToE 𝕩⟩
  }
  Avls ← {map‿r 𝕊 y‿x :
    {
      1≥+´map.Has¨⥊y‿x⊸+¨¯1+↕3‿3 ? 4↑0 ;
      avN ← {¬map.Has⟨y-1,x-1⟩ ? ¬map.Has⟨y-1,x  ⟩ ? ¬map.Has⟨y-1,x+1⟩ ? map.Has⟨y,x⟩ ; 0}
      avS ← {¬map.Has⟨y+1,x-1⟩ ? ¬map.Has⟨y+1,x  ⟩ ? ¬map.Has⟨y+1,x+1⟩ ? map.Has⟨y,x⟩ ; 0}
      avW ← {¬map.Has⟨y-1,x-1⟩ ? ¬map.Has⟨y  ,x-1⟩ ? ¬map.Has⟨y+1,x-1⟩ ? map.Has⟨y,x⟩ ; 0}
      avE ← {¬map.Has⟨y-1,x+1⟩ ? ¬map.Has⟨y  ,x+1⟩ ? ¬map.Has⟨y+1,x+1⟩ ? map.Has⟨y,x⟩ ; 0}
      (r-1)⌽⟨avN,avS,avW,avE⟩
    }
  }
  Locations ← Avls/Moves            # at most 4 cands
  NextLocation ← (¬∘≠⊸↓)∘Locations  # at most 1 location
  { # test hashmap1
    h ← Hashmap˜⟨⟩
    0 h.Set 1
    "h.get/1" lib.Debug h.Get 0
    0 h.Set 1+ 0 h.Get 0
    "h.get/1" lib.Debug h.Get 0
  }
  {
    0=part ?
      Embed ← ¯10⊸(⌽⎉1)·¯10⊸⌽(20+≢)⊸↑
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
      Locations ← Avls/Moves            # at most 4 cands
      NextLocation ← (¬∘≠⊸↓)∘Locations  # at most 1 location
      CountGround ← {𝕊 m :              # sum of empty cells
        "" lib.Debug m
        "area" lib.Debug area ← ×´(¬´¯1‿0⊏∧)˘⍉>alive ← ⊑⟜m¨⊸/⥊↕≢m
        area-≠alive
      }
      CountGround 1⊑{step‿data :
        0 lib.Progress destination ← {data‿(4|step) NextLocation 𝕩}¨↕≢data
        # Aggregate congestion map by using a tricky 0→1→∞ counter then collapse elements by (1=≠)
        0 lib.Progress movedElves ← 1=congestion ← (data≢⊸↑0){𝕨𝕊𝕩 : (÷0⊸=)⌾(𝕨⊸⊑)𝕩}´⥊>⟨⟩⊸≢¨⊸/⥊destination
        # Erase Elves from data if ¬destination⊑congestion
        remainingElves ← {p ← 𝕩⊑destination ⋄ ⟨⟩≢p ? ¬p⊑⊸⊑movedElves ; 𝕩⊑data}¨↕≢data
        ⟨1+step, remainingElves∨movedElves⟩
      }•_while_(10≥⊑) 1‿data ;

    ⊑part∊⟨1,2⟩ ?
      set ← HashSet(⥊·↕≢)⊸((⊑¨⟜<)/⊣)data
      Empties ← {r‿c‿set : alive ← ∧set.Values⁼@ ⋄ alive≠⊸(-˜)×´(¬´¯1‿0⊏∧)˘⍉>alive}
      Step ← {round‿moved‿set :
        numElvesB ← set.Count@
        # build destination that map from Elf to the possible target position
        destinations ← (¬∘≠⊸↓)¨{set‿(4|round) NextLocation 𝕩}¨set.Values⁼@
        {0=round ?
          "destination" lib.Debug >⋈¨destinations
        ;0
        }
        ! numElvesB=≠destinations
        ! ∧´(1≥≠)¨destinations
        congestion ← (HashMap˜⟨⟩){𝕨 𝕩.Set 1+0 𝕩.Get 𝕨}´⥊>⟨⟩⊸≢¨⊸/destinations
        {0=round ?
          "congestion" lib.Debug >⋈¨congestion.Values⁼˜@
          "building" lib.Debug ⍉>(1=1⊸⊑)¨⊸/congestion.Values⁼˜@
        ;0
        }
        movedElves ← HashSet{⟨⟩: ⟨⟩ ; ⊏𝕩}⍉>(1=1⊸⊑)¨⊸/congestion.Values⁼˜@
        # "moved" lib.Debug movedElves.Values⁼˜@
        continue ← 0<movedElves.Count@
        {continue ? 0 ; ∞} lib.Progress round
        # Erase Elves from data if ¬destination⊑congestion
        Pickup ← {now‿⟨⟩ : now ; now‿nexts : ¬movedElves.Has ⊑nexts ? now ; ⟨⟩}
        # "now → next" lib.Debug >destinations⋈˜¨set.Values⁼@
        remainingElves ← (⟨⟩⊸≢)¨⊸/Pickup¨destinations⋈˜¨set.Values⁼@
        movedElves{𝕩.Set 𝕨}´remainingElves
        numElvesA ← movedElves.Count@
        {0=round ?
          "before" lib.Debug ⍉>set.Values⁼@
          "count" lib.Debug ⍉>movedElves.Values⁼@
        ;0
        }
        ⟨round,numElvesA,numElvesB⟩ ! numElvesA=numElvesB
        ⟨1+round,continue,movedElves⟩
      }
      {
        1=part ? Empties Step•_while_(10≥⊑) 1‿1‿set ;
        2=part ? (¯1+⊑)  Step•_while_(1⊸⊑)  1‿1‿set
      }
  }
}
