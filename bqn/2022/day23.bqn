Solve ⇐ {env‿part 𝕊 data :
  lib ← "." env.Var⌾⋈ "BQN_LIB"
  util‿⟨HashMap⟩‿⟨HashSet⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/hashset.bqn"∾˜¨<lib
  Moves ← {map‿r 𝕊 y‿x :
    toN ← {⟨y-1,  x⟩}
    toS ← {⟨y+1,  x⟩}
    toW ← {⟨  y,x-1⟩}
    toE ← {⟨  y,x+1⟩}
    (r-1)⌽⟨toN,toS,toW,toE⟩
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
  Locations ← Avls/Moves                    # at most 4 cands
  NextLocation ← (¬∘≠⊸↓)∘Locations          # at most 1 location
  Empties ← {r‿c‿set : alive ← ∧set.Values⁼@ ⋄ alive≠⊸(-˜)×´(¬´¯1‿0⊏∧)˘⍉>alive}
  Step ← {round‿moved‿set : 
    destinations ← (¬∘≠⊸↓)¨{set‿(4|round) NextLocation 𝕩}¨set.Values⁼@
    congestion ← (HashMap˜⟨⟩){𝕨 𝕩.Set 1+0 𝕩.Get 𝕨}´⥊>⟨⟩⊸≢¨⊸/destinations
    elves ← HashSet{⟨⟩: ⟨⟩ ; ⊏𝕩}⍉>(1=1⊸⊑)¨⊸/congestion.Values⁼˜@
    continue ← 0<elves.Count@
    {continue ? util.Progress round ; ∞ util.Progress round}  
    Move ← {now‿⟨⟩ : elves.Set now ; now‿⟨next⟩ : ¬elves.Has next ? elves.Set now ; ⟨⟩}
    Move¨destinations⋈˜¨set.Values⁼@
    ⟨1+round,continue,elves⟩
  }
  set ← HashSet(⥊·↕≢)⊸((⊑¨⟜<)/⊣)'#'=>data
  {
    1=part ? Empties Step•_while_(10≥⊑) 1‿1‿set ;
    2=part ? (¯1+⊑)  Step•_while_(1⊸⊑)  1‿1‿set
  }
}
