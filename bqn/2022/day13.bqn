#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
problems ← (2⊸↑˘)∘‿3⥊','⊸lib.Tokenize¨∾⟜ ⟨⟨⟩⟩ •FLines "data/2022/input-day13.txt" lib.DataFile •args
Reform ← { data 𝕊 level‿out:
  {
    ∨´"[]"∊data ? (level+((('['⊸=)¨⊸/)(-○≠)((']'⊸=)¨⊸/))data)‿out;
    level‿(out∾⟨⟨level,•BQN data⟩⟩)
  }
}
lib.color.blue lib.term.Println ≢ problems { ⟨0, ⟨⟩⟩ Reform´ ⌽𝕩 }¨˘ ↩
