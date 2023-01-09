#!/usr/bin/env cbqn
⟨color,DataFile,ParseInts,StartsWith,Swap⟩ ← •Import "../lib.bqn"
session ← (⟨⟩⊸≢)¨⊸/{(⟨⟩⊸≢)¨⊸/ " "((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢) 𝕩}¨"$"((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)∾(" "⊸∾˜)¨∘•FLines "data/2022/input-day07.txt" DataFile •args
dirs ← ⟨⟩
Traverse ← { io 𝕊 pwd:
  {
    ⟨"cd"⟩≡io      ? pwd ↩ ⟨"/"⟩;
    ⟨"cd",".."⟩≡io ? pwd (¯1+≠)⊸↑↩;
    "cd"≡⊑io       ? pwd (<1⊑io)⊸(∾˜)↩;
    "ls"≡⊑io ?
      total ← 0
      {"dir"≢𝕨 ? total (•BQN 𝕨)⊸+↩ ⋄ @; @}´˘(2⊸|)¨∘↕∘≠⊸/2↕io
      dirs ⟨⟨∾pwd, total⟩⟩⊸∾↩
  }
  { 0=≠pwd ? ⟨"/"⟩; pwd }
}
⟨⟩Traverse´⌽session
ComponentsOf ← {(𝕩˙(StartsWith˜)⊑)¨⊸/dirs}
eachDir ← (⊑⋈(+´∘((1⊸⊑)¨)∘ComponentsOf⊑))¨dirs
•Show +´(1⊸⊑)¨(100000≥1⊸⊑)¨⊸/eachDir
•Out color.blue color.Fmt "free"⋈ free ← 70000000-1⊸⊑⊑("/"⊸≡⊑)¨⊸/eachDir
•Out color.blue color.Fmt "to be freed"⋈ required ← 30000000 - free
•Show ⊑⊑∧(required⊸<⊑)¨⊸/Swap¨eachDir
