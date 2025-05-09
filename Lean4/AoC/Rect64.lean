-- import Init.Data.Array.Subarray
import Std.Data.HashMap

namespace TwoDimensionalVector64

inductive Dir where | N | E | S | W deriving BEq, Hashable, Repr

instance : ToString Dir where
  toString s := match s with
    | .N => "N"
    | .E => "E"
    | .S => "S"
    | .W => "W"

/--
 2D index by unsigned integers: `UInt64 × UInt64`
-/
abbrev Dim2 := UInt64 × UInt64

def Dim2.toInt64 (v : Dim2) : (Int64 × Int64) := (v.1.toNat.toInt64, v.2.toNat.toInt64)

def NonNegDim (d : UInt64 × UInt64) := 0 ≤ d.fst ∧ 0 ≤ d.snd

partial
def range_list (n : UInt64) : List UInt64 :=
  if n = 0 then
    []
  else
    let n' := n - 1
    range_list n' ++ [n']

def toList' (p : Dim2) : List Dim2 :=
  let rl := range_list p.1
  List.map (fun y ↦ (range_list p.2).map (y, ·)) rl |>.flatten

open Std.HashMap

variable {α : Type}

/--
### A Presentation of bounded 2D spaces

Note: this implementation accept zero space for now.
And It returns the `default` by `·.get (0, 0)`
-/
structure Rect (α : Type) [BEq α] where
  width : UInt64
  vector : Array α
deriving Hashable, Repr

instance [BEq α] : BEq (Rect α) where
  beq a b := a.width == b.width && a.vector == b.vector

private
def fold_n (n : Nat) (l : List α) (h : 0 < n) : List (List α) :=
  if l.length = 0 then
    ([] : List (List α))
  else
    if n < l.length then
      (l.take n) :: fold_n n (l.drop n) h
    else
      ([l] : List (List α))

-- #eval fold_n 3 #[0, 2, 3, 10, 12, 19, 20, 22, 23].toList (by simp)

def Rect.to2Dmatrix {α : Type} [BEq α] (self : Rect α) : List (List α) :=
  let w : Nat := self.width.toNat
  if h : 0 < w then fold_n w self.vector.toList h else []

instance [ToString α] [BEq α] : ToString (Rect α) where
  toString self :=
    let ll := self.to2Dmatrix
    ll.map (fun l ↦ s!"{toString l}\n") |> String.join |> (String.append "\n" ·)

namespace Rect

/-
- return the height
-/
@[inline]
def height [BEq α] (self : Rect α) : UInt64 := self.vector.size.toUInt64 / self.width

/--
- return a new instance fitting to the given Dim2
-/
def ofDim2 [BEq α] (h w : UInt64) (default : α) : Rect α :=
  Rect.mk w (Array.replicate (h * w).toNat default)

/--
- return a new instance of Rect by converting from an 2D array
-/
def of2DMatrix [BEq α] (a : Array (Array α)) : Rect α :=
  have h := a.size.toUInt64
  match h with
  | 0 => Rect.mk 0 #[]
  | _ =>
    let total : UInt64 := a.foldl (fun acc vec ↦ acc + vec.size.toUInt64) 0
    let w := total / h
    let v : Array α := a.foldl Array.append #[]
    Rect.mk w v

/--
- return the `(i,j)`-th element of Mat1 instance
-/
@[inline]
def get [BEq α] (self : Rect α) (p : Dim2) (default : α) : α :=
  self.vector.getD (self.width * p.1 + p.2).toNat default

def validIndex? [BEq α] (self : Rect α) (p : Dim2) : Bool :=
  (self.width * p.1 + p.2).toNat < self.vector.size

@[inline]
def get? [BEq α] [Inhabited α] (self : Rect α) (p : Dim2) : Option α :=
  self.vector[(self.width * p.1 + p.2).toNat]?

/--
- set the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
@[inline]
def set [BEq α] (self : Rect α) (p : Dim2) (val : α) : Rect α :=
  let ix := self.width * p.1 + p.2
  Rect.mk self.width (self.vector.set! ix.toNat val)

/--
- modify the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
@[inline]
def modify [BEq α] (self : Rect α) (p: Dim2) (f : α → α) : Rect α :=
  Rect.mk self.width (self.vector.modify (self.width * p.1 + p.2).toNat f)

@[inline]
def swap [BEq α] [Inhabited α] (self : Rect α) (p q : Dim2) : Rect α :=
  { self with
    vector := Array.swapIfInBounds self.vector
      (self.width * p.fst + p.snd).toNat
      (self.width * q.fst + q.snd).toNat }

-- def r := Rect.of2DMatrix #[#[0,1], #[2,4]]
-- #eval r
-- #eval r.set (Dim2.mk 1 1) 100
-- #eval r.modify (Dim2.mk 1 1) (· + 20) 0
-- #eval r.get (Dim2.mk 0 0) 77
-- #eval r.get (Dim2.mk 1 1) 88
-- #eval r.swap (Dim2.mk 0 0) (Dim2.mk 1 1)

/--
- search an element that satisfies the predicate and return indices or none
-/
def findPosition? [BEq α] (p : Rect α) (f : α → Bool) : Option Dim2 :=
  p.vector.findIdx? f |>.map (fun i ↦  (i.toUInt64 / p.width, i.toUInt64 % p.width))

private partial
def findIdxOnSubarray [BEq α]
    (sa : Subarray α) (limit : Fin sa.size) (sub1 : Fin sa.size) (pred : α → Bool)
    : Option Nat :=
  if pred (sa.get limit)
  then some limit
  else
    match (limit : Nat) with
    | 0 => none
    | _ => findIdxOnSubarray sa (limit.sub sub1) sub1 pred

/--
- search an element in a specific row
-/
def findIdxInRow? [BEq α]
    (p : Rect α) (i : Nat) (pred : α → Bool) : Option (Nat × Nat) :=
  let f := i * p.width.toNat
  let t := (i + 1) * p.width.toNat
  let sa := p.vector.toSubarray f t
  if h : sa.size ≠ 0 then
    have : NeZero sa.size := by simp [neZero_iff, h]
    findIdxOnSubarray sa (Fin.ofNat' sa.size (t - f - 1)) (Fin.ofNat' sa.size 1) pred
      |>.map (i, ·)
  else
    none

-- #eval if let some y := Mat1.of2DMatrix #[#[1,2,3], #[4,5,6]] then y.findIdxInRow? 1 (· == 4) else none

def map {β : Type} [BEq α] [BEq β] (self : Rect α) (f : α → β) : Rect β :=
  { self with vector := self.vector.map f }

def foldl {β : Type} [BEq α] (self : Rect α) (f : β → α → β) (init : β) : β :=
  self.vector.foldl f init

def foldlRows {β : Type} [BEq α]
    (self : Rect α) (f : β → α → β) (init : β) : Array β :=
  Array.range self.width.toNat
    |> .map (fun i =>
      self.vector.toSubarray i (i + self.width.toNat)
        |> Array.ofSubarray
        |>.foldl f init)

def mapRows {β : Type} [BEq α]
    (self : Rect α) (f : Array α → β) :  Array β :=
  Array.range (self.vector.size / self.width.toNat)
    |> .map (fun i => self.vector.toSubarray i (i + self.width.toNat) |> Array.ofSubarray |> f)

def row [BEq α] (self : Rect α) (i : Nat) : Subarray α :=
  let j : Nat := i % (self.vector.size % self.width.toNat)
  let f : Nat := j * self.width.toNat
  let t := f + self.width.toNat
  self.vector.toSubarray f t

def column [BEq α] (self : Rect α) (j : Nat) (default : α) : Array α :=
  Array.range self.width.toNat
    |>.map (fun i ↦ self.get (i.toUInt64, j.toUInt64) default)

def area [BEq α] (self : Rect α) : Nat := self.vector.size

-- @[inline] def index (size : Pos) (p : Pos) : Nat := p.fst * size.snd + p.snd
@[inline]
def toIndex₁ {α : Type} [BEq α] (frame : Rect α) (p : Dim2) : Nat :=
  (frame.width * p.fst + p.snd).toNat

@[inline]
def validateIndex₂ {α : Type} [BEq α] (self : Rect α) (p : Dim2) : Option Dim2 :=
  if p.2 < self.width && self.toIndex₁ p < self.vector.size then some p else none

/-- convert from `Vec2` to valid `Dim2` or `None`
-/
@[inline]
def toIndex₂ {α : Type} [BEq α] (self : Rect α) (ip : Int64 × Int64) : Option Dim2 :=
  if ip.1 < 0 || ip.2 < 0 then none
    else
      let p := (ip.1.toUInt64, ip.2.toUInt64)
      if p.2 < self.width && self.toIndex₁ p < self.vector.size then some p else none

-- @[inline] def index' (size : Pos) (n: Nat) : Pos := (n / size.snd, n % size.snd)
@[inline]
def ofIndex₁ {α : Type} [BEq α] (frame : Rect α) (n : UInt64) : Dim2 :=
  (n / frame.width, n % frame.width)

@[inline]
def enum {α : Type} [BEq α] [Inhabited α] (self : Rect α) : Array (Dim2 × α) :=
  Array.range self.vector.size
    |>.filterMap (fun i ↦
        let p := self.ofIndex₁ i.toUInt64
        if let some val := self.get? p then some (p, val) else none)
--
@[inline]
def range {α : Type} [BEq α] [Inhabited α] (self : Rect α) : Array Dim2 :=
  Array.range self.vector.size
    |>.map (fun i ↦ self.ofIndex₁ i.toUInt64)

/--
 - return a list of all valid `(row, column)` index pairs of the Rect in row-major order
 - rows range from 0 to `self.height - 1`
 - columns range from 0 to `self.width - 1`
-/
def indices {α : Type} [BEq α] [Inhabited α] (self : Rect α) : List Dim2 :=
  List.range (self.height.toNat)
    |>.flatMap (fun y ↦ List.range (self.width.toNat)
    |>.map (y.toUInt64, ·.toUInt64))

end Rect

-- def v := #[true, false, true, false]

-- def x := Rect.mk 2 v
-- def y := Rect.of2DMatrix #[#[(1 : Int), 2, 3], #[4, 5, 6]]

-- #check x
-- #eval x
-- #check y
-- #eval y
-- #check Rect.get
-- #check x.get

-- #eval x.get (Dim2.mk 0 0) false
-- #eval y.get (0, 1) 808
-- #eval y.get (100, 100) (-1)

-- #eval x.set (0, 0) false
-- #eval y.set (1, 1) 10000

end TwoDimensionalVector64
