#!/usr/bin/env cbqn
ToNum ← { "": 0; 𝕩 : •BQN 𝕩 }
# •Show ToNum¨ "333"‿""
lines ← ToNum¨ ⥊ •FLines •wdpath∾ "/"∾ ⊑•args
# •Show lines
elves ← +´¨ 0(+`∘=⊔⊢) lines
# •Show elves
•Show ⊑∨ elves
•Show +´ 3↑∨ elves
