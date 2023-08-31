Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "# data" util.Debug ⍉≍data (util.ParseInts⊸{⟨⟩≡𝕨 ? 𝕩 ; ⊑𝕨}¨" "⊸util.Tokenize)¨ ↩
  util.Debug end ← ≠data
  {
    1=part ?
      {
        pc ← ⊑𝕩
        (pc⊑data){
          "cpy"‿x‿y 𝕊 a‿b‿c‿d : (1+pc)‿a‿b‿c‿d ;
          "inc"‿x 𝕊 a‿b‿c‿d : (1+pc)‿a‿b‿c‿d ;
          "dec"‿x 𝕊 a‿b‿c‿d : (1+pc)‿a‿b‿c‿d ;
          "jnz"‿x‿y 𝕊 a‿b‿c‿d : (1+pc)‿a‿b‿c‿d ;
          (𝕨⋈𝕩)!0
        }1↓𝕩
      }•_while_(end>⊑)0‿0‿0‿0‿0 ;
    0
  }
}
