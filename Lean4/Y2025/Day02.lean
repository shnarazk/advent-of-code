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
def repeatBy (a : UInt64) (n : Nat) : UInt64 :=
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
    total := total + d.repeatBy r
  if ss == ee
  then
    if (1 ... r).iter.all (fun i ↦ ss ≥ s.pick len.toNat i && ss ≤ e.pick len.toNat i) then
     total := total + ss.repeatBy r
  else
    if (1 ... r).iter.all (fun i ↦ ss ≥ s.pick len.toNat i) then
     total := total + ss.repeatBy r
    if (1 ... r).iter.all (fun i ↦ ee ≤ e.pick len.toNat i) then
     total := total + ee.repeatBy r
  total.toNat

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

def solve (input : Input) : Nat := input.line.map (uncurry calcOnRange) |> sum

end Part1

namespace Part2

open Std

def calcOnRange1 (range : UInt64 × UInt64) (total' : HashSet UInt64) : HashSet UInt64 := Id.run do
  let mut total := total'
  let s_len := range.1.iLog10.toNat + 1
  let ss := range.1.pick 1 0
  let ee := range.2 / (10 ^ (s_len - 1))
  for d in ss ...= ee do
    let x := (d.pick 1 0).repeatBy (s_len + d.iLog10.toNat)
    if x ≥ 10 && range.1 ≤ x && x ≤ range.2 then total := total.insert x
  total

def calcOnRangeN (range : UInt64 × UInt64) (len : Nat) (total' : HashSet UInt64) : HashSet UInt64 := Id.run do
  let mut e := range.2
  let e_len := e.iLog10.toNat + 1
  if e_len / len < 2 then return total'
  if e_len % len > 0 then e := 10 ^ ((e_len / len) * len) - 1
  let mut s := range.1
  let mut s_len := s.iLog10.toNat + 1
  if s_len % len > 0 then
    s_len := (s_len / len + 1) * len
    s := 10 ^ (s_len - 1)
  let mut total := total'
  for d in (s.pick len 0) ...= (e.pick len 0) do
    let x := d.repeatBy (s_len / len)
    if s ≤ x && x ≤ e then total := total.insert x
  total

def calcOnRanges (range : UInt64 × UInt64) : Nat := Id.run do
  let mut total : HashSet UInt64 := HashSet.emptyWithCapacity 2
  total := calcOnRange1 range total
  for len in (2 : Nat)...= 8 do total := calcOnRangeN range len total
  total.fold (· + ·) 0 |>.toNat

def solve (input : Input) : Nat := input.line.map calcOnRanges |> sum

end Part2

public def solve := AocProblem.config 2025 02 parser.parse Part1.solve Part2.solve

end Y2025.Day02
