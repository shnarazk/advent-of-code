#!/usr/bin/env cbqn
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1↓↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
util‿loc ← •Import¨ "/util.bqn"‿"/loc.bqn"∾˜¨ "." env.Var< "BQN_LIB"
aoc ← ".." env.Var⌾⋈ "AOC_REPO_DIR"
cw ← 8
Fill ← (cw↑' ')⊸util.LeftFill
⟨year⟩‿targets ← util.ParseInt¨⌾(1⊸⊑)1(↑⋈↓)•args
blacklist ← ∧{
  ⟨⟩≡targets ? 1+↕25 ;
  !(⌊´=⌈´)×¨targets
  (0>⊑targets)◶⟨(¬∘∊⟜targets)⊸/,-targets⟩1+↕25
}
y ← "2020" util.LeftFill year
result ← {
  ∊⟜blacklist⌾⋈ 𝕩 ? 𝕩‿"-"‿"skipped"‿"skipped" ;
  d ← "00" util.LeftFill •Fmt 𝕩
  progfile ← aoc∾"/bqn/"∾y∾"/day"∾d∾".bqn"
  datafile ← aoc∾"/data/"∾y∾"/input-day"∾d∾".txt"
  ∧´•file.Exists¨progfile‿datafile ?
  nl ← loc.LinesOfCode progfile
  bqn ← •Import progfile
  util.Progress "day "∾d
  part1 ← (env‿1⊸bqn.Solve)•_timed •FLines datafile
  part2 ← (env‿2⊸bqn.Solve)•_timed •FLines datafile
  𝕩∾(Fill∘•Fmt)¨nl∾(⌊0.5⊸+)⌾(1000⊸×)¨part1‿part2 ;
  𝕩‿"N/A"‿"N/A"‿"N/A"
}¨1+↕25

•Out "```"
•Out ¯1↓1⊑•SH "cbqn"‿"--version"
•Out "```"
•Out "| y"∾y∾"  | "∾(Fill "LoC")∾" | "∾(Fill "p1 (sec)")∾" | "∾(Fill "p2 (sec)")∾" |"
•Out "|--------|"∾(('-'+(2+cw)↑0)util.LeftFill ":")∾"|"∾(('-'+(2+cw)↑0)util.LeftFill ":")∾"|"∾(('-'+(2+cw)↑0)util.LeftFill ":")∾"|"
{day‿lines‿part1‿part2 :
  •Out "| day "∾("00" util.LeftFill •Fmt day)∾" | "∾(Fill lines)∾" | "∾(Fill part1)∾" | "∾(Fill part2)∾" |"}¨result
