Solve ⇐ {env‿part 𝕊 data :
  util‿geo ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ((⟨"turn of","turn on", "toggle "⟩⊸⊐⌾<(7⊸↑))⋈util.ParseInts)¨ ↩
  shape ← 1000‿1000
  +´⥊{
    1=part ?
      (0¨↕shape){
        0‿⟨y0,x0,y1,x1⟩ 𝕊 v : 𝕩∧⟜¬(-y0‿x0) geo.Rotate shape↑1¨↕⟨y1¬y0,x1¬x0⟩ ;
        1‿⟨y0,x0,y1,x1⟩ 𝕊 v : 𝕩∨(-y0‿x0) geo.Rotate shape↑1¨↕⟨y1¬y0,x1¬x0⟩ ;
        2‿⟨y0,x0,y1,x1⟩ 𝕊 v : 𝕩((¬⊸∧)∨(∧⟜¬))(-y0‿x0) geo.Rotate shape↑1¨↕⟨y1¬y0,x1¬x0⟩
      }´⌽data
    ;
      (0¨↕shape){
        0‿⟨y0,x0,y1,x1⟩ 𝕊 v : 0⌈𝕩-(-y0‿x0) geo.Rotate shape↑1¨↕⟨y1¬y0,x1¬x0⟩ ;
        1‿⟨y0,x0,y1,x1⟩ 𝕊 v : 𝕩+(-y0‿x0) geo.Rotate shape↑1¨↕⟨y1¬y0,x1¬x0⟩ ;
        2‿⟨y0,x0,y1,x1⟩ 𝕊 v : 𝕩+2×(-y0‿x0) geo.Rotate shape↑1¨↕⟨y1¬y0,x1¬x0⟩
      }´⌽data
  }
}
