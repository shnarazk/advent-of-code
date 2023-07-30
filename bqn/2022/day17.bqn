Solve ⇐ {env‿part 𝕊 data :
  lib ← "." env.Var⌾⋈ "BQN_LIB"
  util‿⟨HashMap⟩‿⟨HashSet⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/hashset.bqn"∾˜¨<lib
  "shapes" util.Debug shapes ← [
    shape0 ← <[1‿1‿1‿1]
    shape1 ← <[0‿1‿0,1‿1‿1,0‿1‿0]
    shape2 ← <[0‿0‿1,0‿0‿1,1‿1‿1]
    shape3 ← <[⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩]
    shape4 ← <[1‿1,1‿1]
  ]
  Clash ← {
    0‿pos1 𝕊 0‿pos2 : (1>pos1|∘-○⊑pos2)∧(4>pos1|∘-○(1⊸⊑)pos2) ;
    0‿pos1 𝕊 1‿pos2 : @ ;
    0‿pos1 𝕊 2‿pos2 : @ ;
    0‿pos1 𝕊 3‿pos2 : @ ;
    0‿pos1 𝕊 4‿pos2 : @ ;
    1‿pos1 𝕊 1‿pos2 : @ ;
    1‿pos1 𝕊 2‿pos2 : @ ;
    1‿pos1 𝕊 3‿pos2 : @ ;
    1‿pos1 𝕊 4‿pos2 : @ ;
    2‿pos1 𝕊 2‿pos2 : @ ;
    2‿pos1 𝕊 3‿pos2 : @ ;
    2‿pos1 𝕊 4‿pos2 : @ ;
    3‿pos1 𝕊 3‿pos2 : (4>pos1|∘-○⊑pos2)∧(1>pos1|∘-○(1⊸⊑)pos2) ;
    3‿pos1 𝕊 4‿pos2 : @ ;
    4‿pos1 𝕊 4‿pos2 : (2>pos1|∘-○⊑pos2)∧(2>pos1|∘-○(1⊸⊑)pos2) ;
    a‿pos1 𝕊 b‿pos2 : b‿pos1 𝕊 a‿pos2
  }
  "≠jetPattern" util.Debug ≠jetPattern ← (¯1‿1⊑˜'>'⊸=)¨⊑data
  0
}

