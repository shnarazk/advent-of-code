Solve ⇐ {env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  Part1 ← {a‿b‿x‿y : ((a≤x)∧(y≤b))∨((x≤a)∧(b≤y))}
  Part2 ← {a‿b‿x‿y : (x≤b)∧(a≤y)}
  +´{1=part ? Part1¨𝕩 ; Part2¨𝕩}lib.ParseInts¨{'-' : ',' ; 𝕩}¨¨data
}
