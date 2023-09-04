#!/usr/bin/env cbqn
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1↓↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
util‿loc‿⟨LeftFill⟩← •Import¨"/util.bqn"‿"/loc.bqn"‿"/string.bqn"∾˜¨"." env.Var< "BQN_LIB"
aoc ← ".." env.Var⌾⋈ "AOC_REPO_DIR"
cw ← 8
cwloc ← 3
Fill ← {(cw↑' ')⊸LeftFill 𝕩 ; ( 𝕨↑' ')⊸LeftFill 𝕩}
Add000 ← {
  z ← (¯1+≠s)-(s ← •Repr(⌊0.5⊸+)⌾(1000⊸×)𝕩)⊸⊐⌾⋈'.'
  {
    ¯1=z ? s∾".000" ;
    3>z ? s∾(3-z)↑"000" ;
    s
  }
}
⟨year⟩‿targets ← util.ParseInt¨⌾(1⊸⊑)1(↑⋈↓)•args
blacklist ← ∧{
  ⟨⟩≡targets ? ⟨⟩ ;
  !(⌊´=⌈´)×¨targets
  (0>⊑targets)◶⟨(¬∘∊⟜targets)⊸/,-targets⟩1+↕25
}
y ← "2020" LeftFill year
result ← {𝕊 day :
  d ← "00" LeftFill •Fmt day
  progfile ← aoc∾"/bqn/"∾y∾"/day"∾d∾".bqn"
  nl ← •file.Exists◶⟨"-",loc.LinesOfCode⟩ progfile
  {
    ∊⟜blacklist⌾⋈day ? day‿nl‿"skipped"‿"skipped" ;
    datafile ← aoc∾"/data/"∾y∾"/input-day"∾d∾".txt"
    ∧´•file.Exists¨progfile‿datafile ?
    util.Progress "day "∾d
    bqn ← •Import progfile
    part1 ← (env‿1⊸bqn.Solve)•_timed •FLines datafile
    part2 ← (env‿2⊸bqn.Solve)•_timed •FLines datafile
    day∾nl∾Fill∘Add000¨part1‿part2 ;
    day‿nl‿"N/A"‿"N/A"
  }
}¨1+↕25

•Out ""
•Out "```"
•Out ¯1↓1⊑•SH "cbqn"‿"--version"
•Out "```"
•Out ""
•Out "| y"∾y∾"  | "∾(cwloc Fill "LoC")∾" | "∾(Fill "p1 (sec)")∾" | "∾(Fill "p2 (sec)")∾" |"
•Out "|--------|"∾(('-'+(2+cwloc)↑0)LeftFill ":")∾"|"∾(('-'+(2+cw)↑0)LeftFill ":")∾"|"∾(('-'+(2+cw)↑0)LeftFill ":")∾"|"
{day‿lines‿part1‿part2 :
  •Out "| day "∾("00" LeftFill day)∾" | "∾(cwloc Fill lines)∾" | "∾(Fill part1)∾" | "∾(Fill part2)∾" |"}¨result
•Out ""
