Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  {
    1=part ?
      Count ← {0‿0{
        '\' 𝕊 count‿0 : (count+1)‿1 ;
         𝕨  𝕊 count‿0 : (count+1)‿0 ;
        'x' 𝕊 count‿1 : count‿2 ;
        c 𝕊 count‿n : n > 0 ? count‿(n-1) ;
        !0
      }´⌽𝕩}
     +´((2+≠)-(⊑Count))¨data ;
    Count ← {2+0{
      '\' 𝕊 count : count+2 ;
      '"' 𝕊 count : count+2 ;
       𝕨  𝕊 count : count+1 ;
      !0
    }´⌽𝕩}
   +´(Count-≠)¨data
  }
}
