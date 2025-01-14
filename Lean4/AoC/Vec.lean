import Mathlib.Tactic.Basic
import Mathlib.Tactic.Coe
import Init.Data.Vector
import Init.Data.Array

namespace Dim2

inductive Dir where | N | E | S | W deriving BEq, Hashable, Repr

instance : ToString Dir where
  toString s := match s with
    | .N => "N"
    | .E => "E"
    | .S => "S"
    | .W => "W"

namespace Dir
def turn : Dir → Dir
  | Dir.N => Dir.E
  | Dir.E => Dir.S
  | Dir.S => Dir.W
  | Dir.W => Dir.N
-- #eval Dir.E.turn

lemma turn_four_times_eq_self : ∀ d : Dir, d.turn.turn.turn.turn = d := by
  intro d
  dsimp [turn]
  cases d <;> simp

def asVec₂ : Dir → (Int × Int)
  | Dir.N => (-1,  0)
  | Dir.E => ( 0,  1)
  | Dir.S => ( 1,  0)
  | Dir.W => ( 0, -1)
-- #eval (8, 5) + Dir.N.asVec2

end Dir

abbrev Vec₂ := Int × Int

instance : BEq Vec₂ where beq a b := a.1 == b.1 && a.2 == b.2
-- #eval (0, 0) == (1, 0)
instance : ToString Vec₂ where toString v := s!"({v.1},{v.2})"
instance : Hashable Int64 where hash a := a.toUInt64
-- instance : Hashable Vec₂ where hash a := hash (a.1)o

instance : HAdd Vec₂ Vec₂ Vec₂ where
  hAdd (a b : Vec₂) : Vec₂ := (a.1 + b.1, a.2 + b.2)

instance : HAdd Vec₂ Int Vec₂ where
  hAdd (v : Vec₂) (a : Int) : Vec₂ := (v.1 + a, v.2 + a)

instance : HSub Vec₂ Vec₂ Vec₂ where
  hSub (a b : Vec₂) : Vec₂ := (a.1 - b.1, a.2 - b.2)

instance : HSub Vec₂ Int Vec₂ where
  hSub (v : Vec₂) (a : Int) : Vec₂ := (v.1 - a, v.2 - a)

instance : LT Vec₂ where
  lt (a b : Vec₂) := a.1 < b.1 ∧ a.2 < b.2

instance instDecidableLtVec₂ (a b : Vec₂) : Decidable (a < b) := by
  dsimp [instLTVec₂]
  exact instDecidableAnd

-- #eval ((0, 0) : Vec₂) < ((8, 2) : Vec₂)

instance : LE Vec₂ where
  le (a b : Vec₂) := a.1 ≤ b.1 ∧ a.2 ≤ b.2

instance instDecidableLeVec₂ (a b : Vec₂) : Decidable (a ≤ b) := by
  dsimp [instLEVec₂]
  exact instDecidableAnd

-- #eval ((0, 0) : Vec₂) ≤ ((8, 2) : Vec₂)

def geZeroAndLe (size pos : Vec₂) : Bool := (0, 0) ≤ pos && pos ≤ size

syntax:50 term:51 " ≤₀ " term:50 : term
macro_rules | `($a ≤₀ $b) => `(geZeroAndLe $b $a)

def geZeroAndLt (size pos : Vec₂) : Bool := (0, 0) ≤ pos && pos < size

syntax:50 (name := syntaxInfixGeZeroAndLt) term:51 " <₀ " term:50 : term
macro_rules | `($a <₀ $b) => `(geZeroAndLt $b $a)

-- #eval ((0, 0) : Vec₂) < (3, 2)
-- #eval geZeroAndLt (5, 5) (3, 2)
-- #eval (3, 2) <₀ (5, 5)

-- def Vec₂.toUInt64 (v : Vec₂) : (UInt64 × UInt64) := (v.1.toUInt64, v.2.toUInt64)

/--
  Subtype of `Vec₂` as valid index for `Rect`.
-/
def Idx₂ := { v : Vec₂ // (0, 0) ≤ v }
deriving BEq, Hashable, Repr

instance : ToString Idx₂ where toString v := toString v.val
instance : Coe Idx₂ Vec₂ where coe v := v.1
instance : Coe Idx₂ (Nat × Nat) where coe v := (v.1.1.toNat, v.1.2.toNat)
instance : Coe (Nat × Nat) Idx₂ where coe v :=
  ⟨
    (((↑ v.1) : Int), ((↑ v.2) : Int)),
    by
      constructor
      { simp ; exact Int.ofNat_zero_le v.fst }
      { simp ; exact Int.ofNat_zero_le v.snd }
  ⟩
-- def v : Vec₂ := (1, 1)
-- def d : Idx₂ := ⟨(1, 1), by exact ⟨rfl, rfl⟩⟩
-- #check ((↑ d) : Vec₂)
-- #check ((↑ d) : Idx₂)
-- def w : Vec₂ := (-1, -1)
-- #eval (↑ w)

class RectIndex (α : Type) where
  toIndex₂ : α → Nat × Nat

instance : RectIndex Idx₂ where
  toIndex₂ p := ↑ p

instance : RectIndex (Nat × Nat) where
  toIndex₂ p := p

-- #check RectIndex.toIndex₂ ((↑ d) : Idx₂)

class RectIndexMaybe (α : Type) where
  toIndex₂? : α → Option (Nat × Nat)

instance : RectIndexMaybe Vec₂ where
  toIndex₂? p := if (0, 0) ≤ p then some (p.1.toNat, p.2.toNat) else none

instance : RectIndexMaybe Idx₂ where
  toIndex₂? p := some (↑ p)

instance : RectIndexMaybe (Nat × Nat) where
  toIndex₂? p := some p

-- #check RectIndex.toIndex₂ ((↑ d) : Idx₂)

partial def range_list (n : Int) : List Int := List.range n.toNat |>.map Int.ofNat

def toList' (p : Idx₂) : List Idx₂ :=
  let i : Vec₂ := ↑ p
  let rl := range_list i.1
  List.map (fun y ↦ (range_list i.2).map (y, ·) ) rl
    |>.flatten
    |>.flatMap (fun v ↦ if h : (0, 0) ≤ v then [⟨v, h⟩] else [])

open Std.HashMap Vector

variable {α : Type}

/--
### A Presentation of bounded 2D spaces

Note: this implementation accept zero space for now.
And It returns the `default` by `·.get (0, 0)`
-/
structure Rect (height width : Nat) (α : Type) [BEq α] where
  vector : Vector α (height * width)
deriving Repr

instance [BEq α] : BEq (Rect height width α) where
  beq a b := width == width && a.vector == b.vector

set_option diagnostics true

instance Hashable [BEq α] [Hashable α] : Hashable (Rect height width α) where
  hash a := hash a.vector.toArray

private def fold_n (n : Nat) (l : List α) (h : 0 < n) : List (List α) :=
  if l.length = 0 then
    ([] : List (List α))
  else
    if n < l.length then
      (l.take n) :: fold_n n (l.drop n) h
    else
      ([l] : List (List α))

-- #eval fold_n 3 #[0, 2, 3, 10, 12, 19, 20, 22, 23].toList (by simp)

def Rect.to2Dmatrix {α : Type} [BEq α] (self : Rect height width α) : List (List α) :=
  let w : Nat := width
  if h : 0 < w then fold_n w self.vector.toList h else []

instance [ToString α] [BEq α] : ToString (Rect height width α) where
  toString self :=
    let ll := self.to2Dmatrix
    ll.map (fun l ↦ s!"{toString l}\n") |> String.join |> (String.append "\n" ·)

namespace Rect

/-
- return the height
-/
@[inline]
def height [BEq α] (self : Rect _height width α) : Nat := self.vector.size / width

/--
- return a new instance fitting to the given Dim2
-/
def ofDim2 [BEq α] (h w : Nat) (default : α) : Rect h w α :=
  Rect.mk (mkVector (h * w) default)

/--
- return a new instance of Rect by converting from an 2D array
-/
def of2DMatrix [BEq α] (a : Array (Array α)) (default : α)
    (height : Nat := a.size)
    (width : Nat := (a.foldl (fun acc vec ↦ acc.max vec.size) 0) / height)
    : Rect height width α :=
  let a : Array α := a.foldl Array.append #[]
  Vector.range (height * width) |>.map (fun i ↦ a.getD i default) |> Rect.mk

/--
- return the `(i,j)`-th element of Mat1 instance
-/
@[inline] def get [BEq α] [RectIndex β] (self : Rect _height width α) (p : β) (default : α) : α :=
  let i : Nat × Nat := RectIndex.toIndex₂ p
  self.vector.getD (width * i.1 + i.2) default

def validIndex? [BEq α] [RectIndex β] {height width : Nat} (_self : Rect height width α) (p : β) : Bool :=
  let i : Nat × Nat := RectIndex.toIndex₂ p
  i.1 < height && i.2 < width -- && (width * i.1 + i.2) < self.vector.size

@[inline] def get? [BEq α] [Inhabited α] [RectIndex β] (self : Rect _height width α) (p : β) : Option α :=
  let i : Nat × Nat := RectIndex.toIndex₂ p
  self.vector.get? (width * i.1 + i.2)

/--
- set the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
@[inline] def set [BEq α] [RectIndex β] {height width : Nat} (self : Rect height width α) (p : β) (val : α) : Rect height width α :=
  let i : Nat × Nat := RectIndex.toIndex₂ p
  let ix := width * i.1 + i.2
  Rect.mk (self.vector.set! ix val)

/--
- modify the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
@[inline] def modify [BEq α] [RectIndex β] { height : Nat} (self : Rect height width α) (p: β) (f : α → α) : Rect height width α :=
  let i : Nat × Nat := RectIndex.toIndex₂ p
  let ix := width * i.1 + i.2
  let iu := ix.toUSize
  if h : iu.toNat < height * width then
    let val := f (self.vector.uget iu h)
    Rect.mk (self.vector.setIfInBounds ix val)
  else
    self

@[inline] def swap [BEq α] [Inhabited α] [RectIndex β] { height: Nat } (self : Rect height width α) (p q : β) : Rect height width α :=
  let i : Nat × Nat := RectIndex.toIndex₂ p
  let j : Nat × Nat := RectIndex.toIndex₂ q
  { self with
    vector := Vector.swapIfInBounds self.vector (width * i.fst + i.snd) (width * j.fst + j.snd) }

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
def findPosition? [BEq α] { height : Nat } (p : Rect height width α) (f : α → Bool) : Option Idx₂ :=
  if let some i := p.vector.findIdx? f
    then
      if h : 0 ≤ Int.ofNat (i / width) ∧ 0 ≤ Int.ofNat (i % width)
        then some ⟨(Int.ofNat (i / width), Int.ofNat (i % width)), by exact ⟨h.1, h.2⟩⟩
        else none
    else none

private partial def findIdxOnSubarray [BEq α]
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
def findIdxInRow? [BEq α] { height : Nat }
    (p : Rect height width α) (i : Nat) (pred : α → Bool) : Option (Nat × Nat) :=
  let f := i * width
  let t := (i + 1) * width
  let sa := p.vector.toSubarray f t
  if h : sa.size ≠ 0 then
    have : NeZero sa.size := by simp [neZero_iff, h]
    findIdxOnSubarray sa (Fin.ofNat' sa.size (t - f - 1)) (Fin.ofNat' sa.size 1) pred |>.map (i, ·)
  else
    none

-- #eval if let some y := Mat1.of2DMatrix #[#[1,2,3], #[4,5,6]] then y.findIdxInRow? 1 (· == 4) else none

def map {β : Type} [BEq α] [BEq β] { height : Nat } (self : Rect height width α) (f : α → β) : Rect height width β :=
  { self with vector := self.vector.map f }

def foldl {β : Type} [BEq α] { height : Nat } (self : Rect height width α) (f : β → α → β) (init : β) : β :=
  self.vector.foldl f init

def foldlRows {β : Type} [BEq α] { height : Nat }
    (self : Rect height width α) (f : β → α → β) (init : β) : Array β :=
  Array.range width
    |> .map (fun i =>
      self.vector.toSubarray i (i + width)
        |> Array.ofSubarray
        |>.foldl f init)

def mapRows {β : Type} [BEq α] { height : Nat }
    (self : Rect height width α) (f : Array α → β) :  Array β :=
  Array.range (self.vector.size / width)
    |> .map (fun i => self.vector.toSubarray i (i + width) |> Array.ofSubarray |> f)

def row [BEq α] { height : Nat } (self : Rect height width α) (i : Nat) : Subarray α :=
  let j : Nat := i % (self.vector.size % width)
  let f : Nat := j * width
  let t := f + width
  self.vector.toSubarray f t

def column [BEq α] { height : Nat } (self : Rect height width α) (j : Nat) (default : α) : Array α :=
  Array.range width |>.map (fun i ↦ self.get (i, j) default)

def area [BEq α] { height : Nat } (self : Rect height width α) : Nat := self.vector.size

-- @[inline] def index (size : Pos) (p : Pos) : Nat := p.fst * size.snd + p.snd
@[inline] def toIndex₁ {α : Type} [BEq α] [RectIndex β] { height : Nat } (_frame : Rect height width α) (p : β) : Nat :=
  let i : Nat × Nat := RectIndex.toIndex₂ p
  (width * i.fst + i.snd)

/--
convert from `Vec2` to valid `Dim2` or `None`
-/
@[inline] def toValidIdx₂ {α : Type} [BEq α] [RectIndexMaybe β] { height : Nat } (self : Rect height width α) (p : β) : Option Idx₂ :=
  if let some i := RectIndexMaybe.toIndex₂? p then
        if h: 0 ≤ Int.ofNat i.1 ∧ 0 ≤ Int.ofNat i.2 ∧ i.2 < width ∧ self.toIndex₁ i < self.vector.size
          then some ⟨
              ((↑ i) : Vec₂),
              by constructor ; { simp ; exact h.left } ; { simp ; exact h.right.left }
            ⟩
          else none
    else none

-- @[inline] def index' (size : Pos) (n: Nat) : Pos := (n / size.snd, n % size.snd)
@[inline] def ofIndex₁ {α : Type} [BEq α] { height : Nat } (_frame : Rect height width α) (n : Nat) : Nat × Nat :=
  (n / width, n % width)

@[inline] def enum {α : Type} [BEq α] [Inhabited α] { height : Nat } (self : Rect height width α) : Array ((Nat × Nat) × α) :=
  Array.range self.vector.size
    |>.filterMap (fun i ↦
        let p := self.ofIndex₁ i
        if let some val := self.get? p then some (p, val) else none)
--
@[inline] def range {α : Type} [BEq α] [Inhabited α] { height : Nat } (self : Rect height width α) : Array (Nat × Nat) :=
  Array.range self.vector.size |>.map (fun i ↦ self.ofIndex₁ i)

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

end Rect

end Dim2
