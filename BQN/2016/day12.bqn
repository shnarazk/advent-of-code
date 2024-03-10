Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  end ← ≠data (util.ParseInts⊸{⟨⟩≡𝕨 ? ⊑𝕩 ; ⊑𝕨}¨" "⊸util.Split)¨ ↩
  1⊑{pc‿a‿b‿c‿d :
    Val ← {
      𝕊 'a' : a ;
      𝕊 'b' : b ;
      𝕊 'c' : c ;
      𝕊 'd' : d ;
      𝕊  n  : n
    }
    Set ← {
     'a' 𝕊 𝕩 : a ↩ 𝕩 ;
     'b' 𝕊 𝕩 : b ↩ 𝕩 ;
     'c' 𝕊 𝕩 : c ↩ 𝕩 ;
     'd' 𝕊 𝕩 : d ↩ 𝕩
    }
    {
      'c'‿x‿y : y Set    Val x ⋄ (1+pc)‿a‿b‿c‿d ;
      'i'‿x   : x Set 1 +Val x ⋄ (1+pc)‿a‿b‿c‿d ;
      'd'‿x   : x Set ¯1+Val x ⋄ (1+pc)‿a‿b‿c‿d ;
      'j'‿x‿y : pc (0≠Val x)◶⟨1⊸+,(Val y)⊸+⟩ ↩ ⋄ pc‿a‿b‿c‿d
    }pc⊑data
  }•_while_(end>⊑)0‿0‿0‿(2=part)‿0
}
