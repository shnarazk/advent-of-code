Solve ⇐ {env‿part S data :
  util‿⟨md5⟩ ← •Import¨"/util.bqn"‿"/MD5.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  key ← "wtnhxymk"
  IsPassword ← util.StartsWith⟜"00000"
  Input ← key∾•Repr
  # {𝕩 util.Debug ⋈⟜IsPassword Md5 𝕩}¨"abc3231929"‿"abc5017308"
  {
    1=part ?
      2⊑{found‿count‿result :
        {0=1000|count ? util.Progress found‿count‿result ; @}
        {IsPassword h ← Md5 Input count ? ⟨1+found,1+count,result∾5⊑h⟩ ; ⟨found,1+count,result⟩}
      }•_while_(8>⊑)0‿1000000‿⟨⟩ ;
    2⊑{found‿count‿result :
        {0=1000|count ? util.Progress count‿result ; @}
        {
          IsPassword h ← Md5 Input count ?
          i‿v ← 5‿6⊏h
          ('0'≤i)∧(i<'8') ?
          ' '≡(index ← i-'0')⊑result ? ⟨1+found,1+count,v⌾(index⊸⊑)result⟩ ;
          ⟨found,1+count,result⟩
        }
      }•_while_(8>⊑)0‿2200000‿"        "
  }
}
