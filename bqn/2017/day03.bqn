Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug data util.ParseInt¨ ↩
  SpiralStart ← {
    0 : 1 ;
    1+(¯1+2×𝕩)⋆2
  }
  MDist ← {
    "ring start" util.Debug ringstart ← 1+2⋆˜¯1+2×ring ← ¯1+⌈2÷˜1+√ 𝕩
    {
      𝕩<ringstart+2×ring ? ring+|𝕩-ringstart+¯1+1×ring ;
      𝕩<ringstart+4×ring ? ring+|𝕩-ringstart+¯1+3×ring ;
      𝕩<ringstart+6×ring ? ring+|𝕩-ringstart+¯1+5×ring ;
      𝕩<ringstart+8×ring ? ring+|𝕩-ringstart+¯1+7×ring ;
      !0
    }𝕩
  }
  Position ← {
    ringstart ← 1+2⋆˜¯1+2×ring ← ¯1+⌈2÷˜1+√ 𝕩
    {
      𝕩<ringstart+2×ring ? ⟨-𝕩-ringstart+¯1+1×ring,ring⟩ ;
      𝕩<ringstart+4×ring ? ⟨-ring,-𝕩-ringstart+¯1+3×ring⟩ ;
      𝕩<ringstart+6×ring ? ⟨𝕩-ringstart+¯1+5×ring,-ring⟩ ;
      𝕩<ringstart+8×ring ? ⟨ring,𝕩-ringstart+¯1+7×ring⟩ ;
      !0
    }𝕩
  }
  {
    1=part ? ¯1⊑MDist¨data ;
    data ¯1⊸⊑ ↩
    h ← ⟨0‿0⟩Hashmap⟨1⟩
    -{
      p ← Position 𝕩
      p h.Set value ← +´0⊸h.Get¨p⊸+¨ ¯1+⥊↕3‿3
      (data<value)◶⟨1⊸+,-value⟩𝕩
    }•_while_{0⊸<}1
  }
}
