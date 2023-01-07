#!/usr/bin/env cbqn
⟨color,DataFile,ParseInts,StartsWith⟩ ← •Import "../lib.bqn"
session ← (⟨⟩⊸≢)¨⊸/{(⟨⟩⊸≢)¨⊸/ " "((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢) 𝕩}¨"$"((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)∾(" "⊸∾˜)¨∘•FLines "data/2022/input-day07.txt" DataFile •args 
dirs ← ⟨⟩
Traverse ← { interaction 𝕊 pwd:
  cmd ← ⊑interaction
  {
    "cd"≡cmd ?
      {
        ⟨"cd"⟩≡interaction      ? pwd ↩ ⟨"/"⟩; 
        ⟨"cd",".."⟩≡interaction ? pwd  (¯1+≠)⊸↑↩; 
                                  pwd (<1⊑interaction)⊸(∾˜)↩
      }
      { 0=≠pwd ? pwd ↩ ⟨"/"⟩;@ }
      ; 
    "ls"≡cmd ?
      total ← 0
      # •Out color.green color.Out (∾pwd)∾(": ")∾•Fmt interaction
      {
        "dir" D subdir:
          # •Out color.green color.Out "subdir:"∾subdir
          ⟨⟩;
        size F fname: 
          total (•BQN size)⊸+↩ 
          # •Out color.green color.Out "file:"∾fname
          ⟨⟩;
        w E x:
          color.red color.Fmt "strange ls output format"
          ⟨⟩
      }´˘(2⊸|)¨∘↕∘≠⊸/2↕interaction
      dirs ⟨⟨∾pwd, total⟩⟩⊸∾↩ 
      ;  
    •Out color.red color.Fmt "⟨≢interaction,≢cmd⟩" 
  }
  pwd
}
⟨⟩ Traverse´ ⌽session
ComponentsOf ← {(𝕩˙(StartsWith˜)⊑)¨⊸/dirs}
eachDir ← (⊑⋈(+´∘((1⊸⊑)¨)∘ComponentsOf⊑))¨ dirs
•Show +´(1⊸⊑)¨(100000≥1⊸⊑)¨⊸/ eachDir
dirSizes ← {𝕊 a‿b: b‿a}¨ eachDir
•Out color.blue color.Fmt "used"⋈1⊸⊑⊑("/"⊸≡⊑)¨⊸/eachDir
•Out color.blue color.Fmt "free"⋈free ← 70000000-1⊸⊑⊑("/"⊸≡⊑)¨⊸/eachDir
•Out color.blue color.Fmt "to be freed"⋈required ← 30000000 - free
•Out color.blue color.Fmt ⊑∧(required⊸<⊑)¨⊸/dirSizes
•Show ⊑⊑∧(required⊸<⊑)¨⊸/dirSizes
