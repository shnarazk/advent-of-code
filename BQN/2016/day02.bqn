Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨ "/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data "URDL"⊸⊐¨ ↩
  dirs ← ⟨¯1‿0,0‿1,1‿0,0‿¯1⟩
  map ← HashMap´{1=part ? ⟨⥊⋈⌜˜¯1+↕3,'1'+↕9⟩ ; ⟨(2≥+○|)´¨⊸/⥊⋈⌜˜¯2+↕5,'1'‿9(∾○(+⟜↕´))'A'‿4⟩}
  map.Get¨(<0‿0){map.Has p ← 𝕩+𝕨⊑dirs ? p ; 𝕩}´⟜⌽`data
}
