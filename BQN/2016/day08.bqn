Solve ⇐ {env‿part 𝕊 data :
    lib ← •Import"/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
    Decode ← {
        𝕩 lib.StartsWith "rect"       ? 'E'∾lib.ParseInts 𝕩 ;
        𝕩 lib.StartsWith "rotate col" ? 'C'∾lib.ParseInts 𝕩 ;
        𝕩 lib.StartsWith "rotate row" ? 'R'∾lib.ParseInts 𝕩 ;
        𝕩!0
    }
    Eval ← {
        ⟨'E',w,h⟩ F 𝕩 : ⊑{tmp‿c : ⟨'#'¨⌾((↕w)⊸⊏c⊸⊏)tmp,1+c⟩}•_while_(h⊸>1⊸⊑)𝕩‿0 ;
        ⟨'C',c,n⟩ F 𝕩 : ((-n)⊸⌽)⌾(c⊸⊏˘)𝕩 ;
        ⟨'R',r,n⟩ F 𝕩 : ((-n)⊸⌽)⌾(r⊸⊏)𝕩  ;
        𝕨!0
    }
    screen ← 6‿50⥊'.'˙↕300
    example ← ⟨"rect 3x2","rotate column x=1 by 1","rotate row y=0 by 4","rotate column y=1 by 1"⟩
    {
      1=part ? +´'#'=¨⥊screen Eval´⌽Decode¨data ;
      2=part ? screen Eval´⌽Decode¨data ;
      !0
    }
}
