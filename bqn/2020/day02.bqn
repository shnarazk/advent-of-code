Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data 2⊸(util.ParseInt¨∘↑∾↓)¨∘((4≡≠)¨⊸/)∘("- :"⊸util.Split¨) ↩
  +´{1=part ? {a‿b‿⟨c⟩‿d : (a⊸≤∧b⊸≥)+´c=d}; {a‿b‿⟨c⟩‿d : 1=+´c=d⊏˜¯1+a‿b}}¨data
}
