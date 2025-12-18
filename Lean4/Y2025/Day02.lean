module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser

namespace UInt64

/-- return the number of digits minus one: `0.iLog10 = 0` -/
partial
def iLog10 (a : UInt64) : Int := if a < 10 then 0 else 1 + iLog10 (a / 10)
-- #eval (12809 : UInt64).iLog10

/-- pick up `nth` `size` digits as `UInt64`. `nth` is zero-based and is counted from the top. -/
def pick (a : UInt64) (size nth : Nat) : UInt64 :=
  let len : Nat := (a.iLog10 + 1).toNat
  -- assert! len ≥ size * (nth + 1)
  (a / (10 ^ (len - size * (nth + 1))).toUInt64) % (10 ^ size)
-- #eval pick 112233 2 2
-- #eval pick 112233 3 2

/-- return the number from `a` repeating `n` times -/
def repeat_number (a : UInt64) (n : Nat) : UInt64 :=
  let len : Nat := (a.iLog10 + 1).toNat
  (1...n).iter.fold (fun acc _ ↦ acc * (10 ^ len).toUInt64 + a) a
-- #eval repeat_number 123 4

end UInt64

namespace Y2025.Day02

open Accumulation CiCL

structure Input where
  line : Array (UInt64 × UInt64)
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.line}"


namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_range := do
  (fun (a : Nat) _ (b : Nat) ↦ (a.toUInt64, b.toUInt64)) <$> number <*> pchar '-' <*> number

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Input.mk <$> sepBy1 parse_range (pchar ',')

end parser

namespace Part1

/-- return the number of the satifying numbers in `[s, e]`. `r` is radix. -/
def calcOnRange (s' e' : UInt64) (r : Nat := 2) : Nat := Id.run do
  let mut s := s'
  let mut e := e'
  let mut s_len : Int := s.iLog10 + 1
  let mut e_len : Int := e.iLog10 + 1
  if s_len % r > 0 then
    s_len := (s_len / r + 1) * r
    s := (10 ^ (s_len.toNat - 1)).toUInt64
  if e_len % r > 0 then
    e_len := (e_len / r) * r
    e := (10 ^ e_len.toNat - 1).toUInt64
  if s > e then return 0
  let len := (s.iLog10 + 1) / r
  let mut total := 0
  let ss := s.pick len.toNat 0
  let ee := e.pick len.toNat 0
  for d in (ss + 1) ... ee do
    total := total + d.repeat_number r
  if ss == ee
  then
    if (1 ... r).iter.all (fun i ↦ ss ≥ s.pick len.toNat i && ss ≤ e.pick len.toNat i) then
     total := total + ss.repeat_number r
  else
    if (1 ... r).iter.all (fun i ↦ ss ≥ s.pick len.toNat i) then
     total := total + ss.repeat_number r
    if (1 ... r).iter.all (fun i ↦ ee ≤ e.pick len.toNat i) then
     total := total + ee.repeat_number r
  total.toNat

def solve (input : Input) : Nat := input.line.map (uncurry calcOnRange) |> sum

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

public def solve := AocProblem.config 2025 02 parser.parse Part1.solve Part2.solve

end Y2025.Day02
