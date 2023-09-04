Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ((∧´∊⟜"0123456789")◶⟨⊢,util.ParseInt⟩¨ " "⊸util.Tokenize)¨ ↩
  h ← Hashmap˜⟨⟩
  cached ← Hashmap˜⟨⟩
  set‿and‿lsf‿not‿or‿rsf ← ↕6
  Inject ← {
    o1‿arr‿d             : d h.Set o1 ;
    o1‿"AND"‿o2‿arr‿d    : d h.Set ⟨and,o1,o2⟩ ;
    o1‿"LSHIFT"‿o2‿arr‿d : d h.Set ⟨lsf,o1,o2⟩ ;
        "NOT"‿o1‿arr‿d   : d h.Set ⟨not,o1⟩ ;
    o1‿"OR"‿o2‿arr‿d     : d h.Set ⟨or ,o1,o2⟩ ;
    o1‿"RSHIFT"‿o2‿arr‿d : d h.Set ⟨rsf,o1,o2⟩ ;
    𝕩 ! 0
  }
  Eval ← {
    1‿a‿b : "and " util.Debug 1↓𝕩 ⋄ (2⋆16)|(2⋆16)+⊑1‿16•bit._cast a(1‿1•bit._and○(16‿1•bit._cast∘⋈∘𝕊))b ;
    2‿a‿b : "lft " util.Debug 1↓𝕩 ⋄ (2⋆16)|(2⋆16)+⊑1‿16•bit._cast »⍟2 16‿1•bit._cast⋈𝕊 a ;
    3‿a   : "not " util.Debug 1↓𝕩 ⋄ (2⋆16)|(2⋆16)+⊑1‿16•bit._cast 1‿1•bit._not 16‿1•bit._cast⋈𝕊 a ;
    4‿a‿b : "or  " util.Debug 1↓𝕩 ⋄ (2⋆16)|(2⋆16)+⊑1‿16•bit._cast a(1‿1•bit._or○(16‿1•bit._cast∘⋈∘𝕊))b ;
    5‿a‿b : "rft " util.Debug 1↓𝕩 ⋄ (2⋆16)|(2⋆16)+⊑1‿16•bit._cast «⍟2 16‿1•bit._cast⋈𝕊 a ;
    𝕊 a : 1=•Type a ? "int" util.Debug a ;
    𝕊 a : cached.Has a ? cached.Get a ; x ← 𝕊 h.Get "sym" util.Debug 𝕩 ⋄ 𝕩 cached.Set x ⋄ x
  }
  {
    1=part ?
       Inject¨data
       # Eval¨"f"‿"g"‿"h"‿"i"‿"d"‿"e"
       Eval "a"
       cached.Values⁼˜@
      ;
    0
  }
}
