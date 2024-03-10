Solve ⇐ {env‿part 𝕊 data :
  lib ← "." env.Var⌾⋈ "BQN_LIB"
  util‿⟨HashMap⟩‿⟨HashSet⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/hashset.bqn"∾˜¨<lib
  Moves ← {map‿r 𝕊 y‿x : (r-1)⌽⟨⟨y-1,x⟩,⟨y+1,x⟩,⟨y,x-1⟩,⟨y,x+1⟩⟩}
  dirs ← 0‿0⊸≢¨⊸/⥊¯1+↕3‿3
  Avls ← {
    ¬(⊑𝕨).Has𝕩 ? 4↑0 ;
    map‿r ← 𝕨
    nw‿n‿ne‿w‿e‿sw‿s‿se ← ¬map.Has∘(𝕩⊸+)¨dirs
    dirs ← ∧´¨⟨⟨nw,n,ne⟩,⟨sw,s,se⟩,⟨nw,w,sw⟩,⟨ne,e,se⟩⟩
    {∧´dirs ? 4↑0 ; (r-1)⌽dirs}
  }
  Locations ← Avls/Moves                    # at most 4 cands
  NextLocation ← (¬∘≠⊸↓)∘Locations          # at most 1 location
  Empties ← {r‿c‿set : alive ← ∧set.Values⁼@ ⋄ alive≠⊸(-˜)×´(¬´¯1‿0⊏∧)˘⍉>alive}
  Step ← {round‿moved‿set :
    destinations ← (¬∘≠⊸↓)¨{set‿(4|round) NextLocation 𝕩}¨set.Values⁼@
    congestion ← (HashMap˜⟨⟩){𝕨 𝕩.Set 1+0 𝕩.Get 𝕨}´⥊>⟨⟩⊸≢¨⊸/destinations
    elves ← HashSet{⟨⟩: ⟨⟩ ; ⊏𝕩}⍉>(1=1⊸⊑)¨⊸/congestion.Values⁼˜@
    continue ← 0<elves.Count@
    util.Progress round
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
