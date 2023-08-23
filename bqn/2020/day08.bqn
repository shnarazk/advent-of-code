Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data (util.ParseInt⌾(1⊸⊑)" "⊸util.Tokenize)¨ ↩
  {
    1=part ?
      ⊑{𝕊 acc‿pc‿counts :
        counts (1⊸+)⌾(pc⊸⊑) ↩
        {
          2=pc⊑counts ? ⟨acc,pc,counts⟩ ;
          {
            "acc"‿o : pc‿acc (1‿o⊸+) ↩ ;
            "jmp"‿o : pc       (o⊸+) ↩ ;
            "nop"‿o : pc       (1⊸+) ↩
          }pc⊑data
        }
        ⟨acc,pc,counts⟩
      }•_while_(2>(⌈´2⊸⊑))⟨0,0,data≠⊸↑0⟩ ;
    variations ← ("acc"≢⊑)¨⊸/⟜(↕≠)data
    ops ← ≠data
    Flip ← {{"jmp"≡𝕩}◶⟨"jmp","nop"⟩⌾(⊑(𝕩⊑variations)⊸⊑)𝕨}
    Executor ← {𝕊 instructions :
      {acc‿pc‿o : ⟨ops≠pc,acc⟩}{𝕊 acc‿pc‿counts :
        counts (1⊸+)⌾(pc⊸⊑) ↩
        {
          2=pc⊑counts ? ⟨acc,pc,counts⟩ ;
          {
            "acc"‿o : pc‿acc (1‿o⊸+) ↩ ;
            "jmp"‿o : pc       (o⊸+) ↩ ;
            "nop"‿o : pc       (1⊸+) ↩
          }pc⊑instructions
        }
        ⟨acc,pc,counts⟩
      }•_while_{acc‿pc‿counts : (0≤pc)∧(ops>pc)∧2>⌈´counts}⟨0,0,ops↑0⟩
    }
    1⊑{𝕊 notfound‿n : {¬⊑res ← Executor data Flip n ? res ; ⟨1,1+n⟩}}•_while_⊑1‿0
  }
}
