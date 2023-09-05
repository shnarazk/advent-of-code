Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ((∧´∊⟜"0123456789")◶⟨⊢,util.ParseInt⟩¨ " "⊸util.Tokenize)¨ ↩
  h ← Hashmap˜⟨⟩
  cached ← Hashmap˜⟨⟩
  not‿and‿or‿lsf‿rsf ← ↕5
  Inject ← {
    𝕨 𝕊 o1‿"->"    ‿d        : d 𝕨.Set o1 ;
    𝕨 𝕊    "NOT"   ‿o1‿arr‿d : d 𝕨.Set not‿o1 ;
    𝕨 𝕊 o1‿"AND"   ‿o2‿arr‿d : d 𝕨.Set and‿o1‿o2 ;
    𝕨 𝕊 o1‿"OR"    ‿o2‿arr‿d : d 𝕨.Set or‿o1‿o2 ;
    𝕨 𝕊 o1‿"LSHIFT"‿o2‿arr‿d : d 𝕨.Set lsf‿o1‿o2 ;
    𝕨 𝕊 o1‿"RSHIFT"‿o2‿arr‿d : d 𝕨.Set rsf‿o1‿o2 ;
    𝕩 ! 0
  }
  ToBits ← {𝕊 x : 32‿1•bit._cast⋈𝕩 ; 𝕊⁼ x : ⊑⟨1,32⟩•bit._cast 32↑16↑𝕩}
  Eval ← {
    0‿a   : 1‿1•bit._not⌾ToBits 𝕊 a ;
    1‿a‿b : ToBits⁼a(1‿1•bit._and○(ToBits∘𝕊))b ;
    2‿a‿b : ToBits⁼a(1‿1•bit._or○(ToBits∘𝕊))b ;
    3‿a‿b : »⍟b⌾ToBits 𝕊 a ;
    4‿a‿b : «⍟b⌾ToBits 𝕊 a ;
      𝕊 a : cached.Has a ? cached.Get a ;
      𝕊 a : 1=•Type a ? a ;
      𝕊 a : a cached.Set x ← 𝕊 h.Get a ⋄ x
  }
  h Inject¨data
  b ← Eval "a"
  {
    2=part ?
      cached ↩ Hashmap˜⟨⟩
      (h ↩ Hashmap˜⟨⟩)Inject¨data
      "b" h.Set b
      Eval "a" ;
    b
  }
}
