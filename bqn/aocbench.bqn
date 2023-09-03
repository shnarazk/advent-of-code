#!/usr/bin/env cbqn
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1↓↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
util‿loc ← •Import¨"/util.bqn"‿"/loc.bqn"∾˜¨"." env.Var< "BQN_LIB"
aoc ← ".." env.Var⌾⋈ "AOC_REPO_DIR"
cw ← 8
cwloc ← 3
Fill ← {
  (cw↑' ')⊸util.LeftFill(1=•Type)◶⟨⊢,•Repr⟩𝕩 ;
  ( 𝕨↑' ')⊸util.LeftFill(1=•Type)◶⟨⊢,•Repr⟩𝕩
}
⟨year⟩‿targets ← util.ParseInt¨⌾(1⊸⊑)1(↑⋈↓)•args
blacklist ← ∧{
  ⟨⟩≡targets ? ⟨⟩ ;
  !(⌊´=⌈´)×¨targets
  (0>⊑targets)◶⟨(¬∘∊⟜targets)⊸/,-targets⟩1+↕25
}
y ← "2020" util.LeftFill year
result ← {𝕊 day :
  d ← "00" util.LeftFill •Fmt day
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
    day∾nl∾Fill¨(⌊0.5⊸+)⌾(1000⊸×)¨part1‿part2 ;
    day‿nl‿"N/A"‿"N/A"
  }
}¨1+↕25

•Out ""
•Out "```"
•Out ¯1↓1⊑•SH "cbqn"‿"--version"
•Out "```"
•Out ""
•Out "| y"∾y∾"  | "∾(cwloc Fill "LoC")∾" | "∾(Fill "p1 (sec)")∾" | "∾(Fill "p2 (sec)")∾" |"
•Out "|--------|"∾(('-'+(2+cwloc)↑0)util.LeftFill ":")∾"|"∾(('-'+(2+cw)↑0)util.LeftFill ":")∾"|"∾(('-'+(2+cw)↑0)util.LeftFill ":")∾"|"
{day‿lines‿part1‿part2 :
  •Out "| day "∾(2 Fill day)∾" | "∾(cwloc Fill lines)∾" | "∾(Fill part1)∾" | "∾(Fill part2)∾" |"}¨result
•Out ""
