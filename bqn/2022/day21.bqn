Solve ⇐ {env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  dict ← {
    Cannonize ← {2=≠𝕩 ? ⟨⊑𝕩,•BQN 1⊑𝕩⟩; ⟨⊑𝕩, 1↓𝕩⟩}
    table ⇐ ⍉>Cannonize¨" :"⊸lib.Tokenize¨ data
    Search ⇐ {((⊏table)⊐⋈𝕩)⊑1⊏table}
    SetHumn ⇐ {table ↩ 𝕩⌾(((⊏table)⊐⋈"humn")⊸⊑1⊸⊏)table}
  }
  Op ← {"-"≡𝕨 ? -´𝕩 ; "+"≡𝕨 ? +´𝕩 ; "*"≡𝕨 ? ×´𝕩 ; "/"≡𝕨 ? ⌊÷´𝕩 ; 𝕨!0}
  Eval ← {E 𝕩 : { ⟨l,o,r⟩ : o Op E¨l‿r ; 𝕩 }dict.Search 𝕩  }
  {
    1=part ?
      "search root" lib.Debug dict.Search "root"
      Eval "root"
      ;
     2=part ?
      l‿o∞‿r ← dict.Search "root"
      Seek ← {lower S upper :
        !lower<upper
        mid ← ⌊2÷˜lower+upper
        dict.SetHumn mid
        lib.Debug lower‿mid‿upper∾-´l ⋈○Eval r ⋄ lib.term.Up 1 ⋄ lib.term.Out lib.term.clear
        l {𝕨>𝕩 ? mid S upper ; 𝕨<𝕩 ? lower S mid ; mid}○Eval r
      }
      -⊸Seek 2⋆50
      ;
    !0
  }
}
