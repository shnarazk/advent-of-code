Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜ "," env.Var⌾⋈ "BQN_LIB"
  lines ← >(¯5⊸↓⋈¯4⊸↑)¨(" "⊸util.Tokenize)¨data
  Common ← {((¯1+≠𝕩)=⊒)⊸/∾𝕩}
  "Common abe‿ace‿bce"!'e'≡⊑Common "abe"‿"ace"‿"bce"
  Diff ← {common ← Common 𝕩 ⋄ (¬∘⊑∊⟜common˜)¨⊸/⍷∾𝕩}
  "Diff abe‿ace‿bce"!"abc"≡Diff "abe"‿"ace"‿"bce"
  {
    1=part ? util.Debug +´≠¨(<·(⊑⟨2,4,3,7⟩∊˜≠)¨⊸/1⊸⊑)⎉1 lines ;
    segments ← {⟨∧¨¨≠¨⊸⊔𝕨,𝕩⟩}´˘(-⟜'a'˜)¨lines
    # 5-segment digits: 2,3,5 → common segments: adg
    # 6-segment digits: 0,6,9 → common segmests: abfg
    # So all 5-or-6 segments digits contains ⟨a,g⟩
    # but  a is induced from ⟨3-segment digit⟩ - ⟨2-segment digit⟩
    +´⥊{𝕊 dg‿output :
      !1=≠Diff⊑¨2‿3⊏dg
      a ← ⊑Diff⊑¨2‿3⊏dg
      !1=≠Diff⟨a⟩⋈Common(5⊑dg)∾6⊑dg
      g ← ⊑Diff⟨a⟩⋈Common(5⊑dg)∾6⊑dg
      !1=≠Diff⟨a,g⟩⋈ Common 5⊑dg
      d ← ⊑Diff⟨a,g⟩⋈ Common 5⊑dg
      !1=≠Diff⟨d⟩⋈Diff⊑¨2‿4⊏dg
      b ← ⊑Diff⟨d⟩⋈Diff⊑¨2‿4⊏dg
      !1=≠Diff⟨g⟩⋈Diff(↕7)⋈⍷∾⊑¨3‿4⊏dg
      e ← ⊑Diff⟨g⟩⋈Diff(↕7)⋈⍷∾⊑¨3‿4⊏dg
      !1=≠Diff⟨a,b,g⟩⋈ Common 6⊑dg
      f ← ⊑Diff⟨a,b,g⟩⋈ Common 6⊑dg
      c ← ⊑Diff⟨a,b,d,e,f,g⟩⋈↕7
      !(↕7)≡∧⟨a,b,c,d,e,f,g⟩
      "# sum" util.Debug 0{𝕨+10×𝕩}´⌽{
        ⟨a,b,c,e,f,g⟩≡○∧𝕩 ? 0 ;
        ⟨c,f⟩≡○∧𝕩 ? 1 ;
        ⟨a,c,d,e,g⟩≡○∧𝕩 ? 2 ;
        ⟨a,c,d,f,g⟩≡○∧𝕩 ? 3 ;
        ⟨b,c,d,f⟩≡○∧𝕩 ? 4 ;
        ⟨a,b,d,f,g⟩≡○∧𝕩 ? 5 ;
        ⟨a,b,d,e,f,g⟩≡○∧𝕩 ? 6 ;
        ⟨a,c,f⟩≡○∧𝕩 ? 7 ;
        ⟨a,b,c,d,e,f,g⟩≡○∧𝕩 ? 8 ;
        ⟨a,b,c,d,f,g⟩≡○∧𝕩 ? 9 ;
        "strange in output" util.Debug output
        (⟨a,b,c,d,d,e,f⟩∊𝕩)!0
      }¨output
    }˘segments
  }
}
