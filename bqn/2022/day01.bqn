#!/usr/bin/env cbqn
ToNum ← {
  "": 0;
  𝕩 : •BQN 𝕩
}
# •Show (ToNum "333")
# •Show (ToNum "")
lines ← ToNum¨ ⥊ •FLines "../../data/2022/input-day01.txt"
# •Show lines
elves ← +´¨ 0(+`∘=⊔⊢) lines
# •Show elves
•Show ⊑∨ elves
