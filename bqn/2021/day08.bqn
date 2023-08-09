Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜ "," env.Var⌾⋈ "BQN_LIB"
  lines ← >(¯5⊸↓⋈¯4⊸↑)¨(" "⊸util.Tokenize)¨data
  Union ← {((¯1+≠𝕩)=⊒)⊸/∾𝕩}
  "Union abe‿ace‿bce"!'e'≡⊑Union "abe"‿"ace"‿"bce"
  Diff ← {common ← Union 𝕩 ⋄ ⍷(¬∘⊑∊⟜common˜)¨⊸/∾𝕩}
  "Diff abe‿ace‿bce"!"abc"≡Diff "abe"‿"ace"‿"bce"
  {
    1=part ? util.Debug +´≠¨(<·(⊑⟨2,4,3,7⟩∊˜≠)¨⊸/1⊸⊑)⎉1 lines ;
    "segments" util.Debug 5↑segments ← (∧¨¨·≠¨⊸⊔⊑)˘(-⟜'a'˜)¨lines
    # 5-segment digits: 2,3,5 → common segments: adg
    # 6-segment digits: 0,6,9 → common segmests: abfg
    # So all 5-or-6 segments digits contains ⟨a,g⟩
    # but  a is induced from ⟨3-segment digit⟩ - ⟨2-segment digit⟩
    0
  }
}
