Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ⊑ ↩
  {
    1=part ?
      2⊑0‿0‿0{w 𝕊 level‿garbage‿something :
        {
          2=garbage ? garbage ↩ 1 ;
          ','=w ? @ ;
          ('{'=w)∧¬garbage ? level 1⊸+ ↩ ⋄ something level⊸+ ↩ ;
          ('}'=w)∧¬garbage ? level ¯1⊸+ ↩ ;
          ('<'=w)∧¬garbage ? garbage ↩ 1 ;
          ('>'=w)∧ garbage ? garbage ↩ 0 ;
          ('!'=w)∧ garbage ? garbage ↩ 2 ;
          garbage ? @ ;
          w‿garbage!0
        }
        level‿garbage‿something
      }´⌽data
    ;
    2⊑0‿0‿0{w 𝕊 level‿garbage‿something :
      {
        2=garbage ? garbage ↩ 1 ;
        ','=w ? something garbage⊸+ ↩ ;
        ('{'=w)∧¬garbage ? level 1⊸+ ↩ ;
        ('}'=w)∧¬garbage ? level ¯1⊸+ ↩ ;
        ('<'=w)∧¬garbage ? garbage ↩ 1 ;
        ('>'=w)∧ garbage ? garbage ↩ 0 ;
        ('!'=w)∧ garbage ? garbage ↩ 2 ;
        garbage ? something 1⊸+ ↩ ;
        w‿garbage!0
      }
      level‿garbage‿something
    }´⌽data
  }
}
