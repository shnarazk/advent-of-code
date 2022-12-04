#!/usr/bin/env cbqn
⟨ DataFile⟩ ← •Import "../lib.bqn"
ToNum ← { "": 0; 𝕩 : •BQN 𝕩 }
# •Show ToNum¨ "333"‿""
lines ← ToNum¨ ⥊ •FLines "data/2022/input-day01.txt" DataFile •args
elves ← +´¨ 0(+`∘=⊔⊢) lines
•Show ⊑∨ elves
•Show +´ 3↑∨ elves
