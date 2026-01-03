module

public import WinnowParsers
public import «AoC».Basic
public import «AoC».Combinator

namespace Y2025.Day03

open Accumulation

structure Input where
  line : Array (Array Nat)
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.line}"

def toJolt (len : Nat) (v : Array Nat) : Nat := Id.run do
  let mut stack := v[(v.size - len)...v.size].toArray
  for r in len ... v.size do
    let i := v.size - r - 1
    let mut n := v[i]!
    for j in 0 ... len do
      if stack[j]! <= n
      then
        let tmp := stack[j]!
        stack := stack.set! j n
        n := tmp
      else break
  return stack.foldl (fun acc n ↦ acc * 10 + n) 0

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line := many1 ((·.toNat - '0'.toNat) <$> digit)

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Input.mk <$> separated parse_line eol

end parser

def solve₁ (input : Input) : Nat := input.line.map (toJolt 2) |> sum

def solve₂ (input : Input) : Nat := input.line.map (toJolt 12) |> sum

public def solve := AocProblem.config 2025 03 parser.parse solve₁ solve₂

end Y2025.Day03
