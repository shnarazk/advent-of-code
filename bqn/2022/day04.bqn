lib ← •Import"../lib.bqn"
Part1 ← {a‿b‿x‿y : ((a≤x)∧(y≤b))∨((x≤a)∧(b≤y))}
Part2 ← {a‿b‿x‿y : (x≤b)∧(a≤y)}
Solve ⇐  +´{env‿part 𝕊 𝕩 : 1=part ? Part1¨𝕩 ; Part2¨𝕩}⟜(lib.ParseInts¨{'-' : ',' ; 𝕩}¨¨)
