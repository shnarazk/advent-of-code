Solve ⇐ {env‿part 𝕊 line :
  lib ← •Import "/util.bqn"∾˜∾env.Var<"BQN_LIB"
  data ← >{
    4‿4⥊⟨
          1⊑𝕩,   0,   0,  0,
          2⊑𝕩,   0,   0,  0,
          3⊑𝕩, 4⊑𝕩,   0,  0,
          5⊑𝕩,   0, 6⊑𝕩,  0,
        ⟩
  }∘lib.ParseInts¨line
  Examine ← {u 𝕊 n :
    best‿bp‿upto ← ⟨0,n⊏data,-u⟩
    masks‿limits ← ⟨0<˘bp,0‿0‿0‿∞⌈⌈´˘⍉bp⟩
    Expand ← {
      𝕊 ⟨⟩ : best ;
      𝕊 cands :
        𝕊∧⟨⟩{time‿resources‿robots 𝕊 next :
          {𝕊 i :
            upto< t ← time-w ← 1+⌈⌈´(i⊏masks)/robots÷˜(n ← i⊏bp)(0⊸⌈-)resources ?
              {¬∨´(∧´𝕩⊸≤)¨next ? next ⟨𝕩⟩⊸∾ ↩, best ((4⊑𝕩)+(t-upto)×¯1⊑𝕩)⊸⌈ ↩ ; @
              }t∾(n-˜resources+w×robots)∾((1⊸+)⌾(i⊸⊑)robots)
            ; @
          }¨{robots<○(𝕩⊸⊑)limits }¨⊸/↕4
          next
        }´{⟨⊑𝕩,4↑1↓𝕩,5↓𝕩⟩}¨cands
    }
    (•Fmt n)lib.Debug Expand⟨⟨0⟩∾⟨0,0,0,0⟩∾⟨1,0,0,0⟩⟩ # ⟨time,resources,robots⟩
  }
  {
    1=part ? +´24((1⊸+)×Examine)¨↕≠data ;
    2=part ? ×´32 Examine¨ ↕3 ;
             "≢data" lib.Debug ≢data
  }
}
