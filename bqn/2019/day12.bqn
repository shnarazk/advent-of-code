Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  {
    1=part ?
      +´{(+´|𝕨)×(+´|𝕩)}´˘⍉>{position‿velocity :
        velocity ((<+´)˘(×-)˜⌜˜position)⊸+ ↩
        ⟨"# positions" util.Debug position+velocity,velocity⟩
      }⍟1000 ⋈⟜(0¨¨)util.ParseInts¨data
      ;
    data util.ParseInts¨ ↩
    h ← hashmap˜⟨⟩
    •math.lcm´¯1⊑{step‿position‿velocity‿cycle :
      velocity ((<+´)˘(×-)˜⌜˜position)⊸+ ↩
      position velocity⊸+ ↩
      {𝕊 i:
        mask ← (i⌽3↑1)
        key ← ⟨i⟩∾((∾mask⊸/¨)˘position)∾((∾mask⊸/¨)˘velocity)
        {h.Has key ? {(0=i⊑cycle) ? cycle (step-h.Get key)⌾(i⊸⊑) ↩ ; @} ;
         key h.Set step}
      }¨↕3
      util.Progress h.Count@
      ⟨1+step,position,velocity,cycle⟩
    }•_while_(∨´0=¯1⊸⊑)⟨0,data,0¨¨data,0‿0‿0⟩
  }
}
