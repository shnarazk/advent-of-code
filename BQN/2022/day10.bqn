Solve ⇐ {env‿part 𝕊 lines :
  states ← ⟨0,0⟩∾1+`∾{F "noop" : ⟨0⟩ ; ⟨0,•BQN 5↓𝕩⟩}¨lines
  {1=part ?
    ss ← ×¨⟜(↕≠)states
    +´ss⊸(⊑⊏˜)¨⟨20,60,100,140,180,220⟩
  ;
    shifts ← ∾{(𝕩×40)¨↕40}¨↕6
    sprites ← shifts+240↑1↓states
    6‿∘⥊(⊑" #"⊏˜1⊸≥)¨|¨sprites-↕240
  }
}
