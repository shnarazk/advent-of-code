#!/usr/bin/env cbqn
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1↓↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
util‿aoc ← (•Import∾⟜"/util.bqn")⊸⋈´ "."‿".." env.Var "BQN_LIB"‿"AOC_REPO_DIR"
Fill ← "       "⊸util.LeftFill
⟨year⟩‿blacklist ← util.ParseInt¨⌾(1⊸⊑)1(↑⋈↓)•args
blacklist ↩ {
  ⟨⟩≡blacklist ? ⟨⟩ ;
  !(⟨⟩≡blacklist)∨(⌊´=⌈´)×¨blacklist
  (0>⊑blacklist)◶⟨⊢,{(¬∊⟜𝕩)⊸/⌾- 1+↕25}⟩blacklist
}
y ← "2020" util.LeftFill year
result ← {
  ∊⟜blacklist⌾⋈ 𝕩 ? 𝕩‿"skipped"‿"skipped" ;
  d ← "00" util.LeftFill •Fmt 𝕩
  progfile ← aoc∾"/bqn/"∾y∾"/day"∾d∾".bqn"
  datafile ← aoc∾"/data/"∾y∾"/input-day"∾d∾".txt"
  ∧´•file.Exists¨progfile‿datafile ?
  bqn ← •Import progfile
  util.Progress "day "∾d
  part1 ← (env‿1⊸bqn.Solve)•_timed •FLines datafile
  part2 ← (env‿2⊸bqn.Solve)•_timed •FLines datafile
  𝕩∾(Fill∘•Fmt)¨(⌊0.5⊸+)⌾(1000⊸×)¨part1‿part2 ;
  𝕩‿"N/A"‿"N/A"
}¨1+↕25

•Out "```"
•Out ¯1↓1⊑•SH "cbqn"‿"--version"
•Out "```"
•Out "| y"∾y∾"  |  part 1 |  part 2 |"
•Out "|--------|--------:|--------:|"
{day‿part1‿part2 : •Out "| day "∾("00" util.LeftFill •Fmt day)∾" | "∾(Fill part1)∾" | "∾(Fill part2)∾" |"}¨result
