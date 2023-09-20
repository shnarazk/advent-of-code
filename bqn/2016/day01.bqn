Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashset⟩ ← •Import¨ "/util.bqn"‿"/hashset.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ↩ ((1-2×'L'⊸=)∘⊑⋈util.ParseInt)¨ ", " util.Split⊑data
  {
    1=part ? +○|´1⊑0‿⟨0,0⟩{d‿l 𝕊 dir‿pos : ⟨dir 4⊸|∘(d⊸+) ↩ ,pos+l×dir⊑⟨¯1‿0,0‿1,1‿0,0‿¯1⟩⟩}´⌽data ;
    +○|´2⊑{flag‿dir‿pos‿route‿set :
      ⟨d‿l⟩‿remain ← 1(↑⋈↓)route
      dir 4⊸|∘(d⊸+) ↩
      1↓{l‿flag‿dir‿pos‿route‿set :
        pos ↩ pos+dir⊑⟨¯1‿0,0‿1,1‿0,0‿¯1⟩
        {set.Has pos ? ⟨0,0,dir,pos,remain,set⟩ ; ⟨¯1+l,1,dir,pos,remain,set.Set pos⟩}
      }•_while_(0<⊑)⟨l,1,dir,pos,remain,set⟩
    }•_while_⊑⟨1,0,0‿0,data,Hashset⟨0‿0⟩⟩
  }
}
