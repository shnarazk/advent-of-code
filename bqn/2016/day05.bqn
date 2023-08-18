key ← "wtnhxymk"

Solve ⇐ {env‿part S data :
  util‿⟨md5⟩ ← •Import¨"/util.bqn"‿"/MD5.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  # Md5 ← {¯1↓1⊑ •SH "md5"‿"-qs"‿𝕩}
  IsPassword ← util.StartsWith⟜"00000"
  Input ← key∾•Repr
  {𝕩 util.Debug ⋈⟜IsPassword Md5 𝕩}¨"abc3231929"‿"abc5017308"
  •Show{found‿count‿result :
    {0=1000|count ? util.Progress found‿count ; @}
    {IsPassword h ← Md5 Input count ? ⟨1+found,1+count,result∾6⊑h⟩ ; ⟨found,1+count,result⟩}
  }•_while_(8>⊑)0‿1000000‿⟨⟩
}
