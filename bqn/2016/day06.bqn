example ← 6↑˘∘‿7⥊"eedadn
drvtee
eandsr
raavrd
atevrs
tsrnev
sdttsa
rasrtv
nssdts
ntnada
svetve
tesnvt
vntsnd
vrdear
dvrsen
enarar
"

Solve ⇐ {env‿part S data :
  _pick ← {F _𝕣 x : (⊑1⊸⊑)˘{⊑F((≠⊸⋈)¨)⊐⊸⊔𝕩}˘x}
  {
    0=part ? ⟨env‿1 S example,env‿2 S example⟩ ;
    1=part ? ∨_pick⍉>data ;
    2=part ? ∧_pick⍉>data ;
    !0
  }
}
