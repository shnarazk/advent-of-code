module

public import Std.Data.HashMap

@[expose] public section

namespace Dim2

variable {α β γ : Type}

/-- symbols for 4 directions -/
inductive Dir where | N | E | S | W deriving BEq, Hashable, Repr

instance : ToString Dir where
  toString s := match s with
    | .N => "N"
    | .E => "E"
    | .S => "S"
    | .W => "W"

namespace Dir

/-- return the direction after 90-degree clock-wise rotation -/
def turn : Dir → Dir
  | Dir.N => Dir.E
  | Dir.E => Dir.S
  | Dir.S => Dir.W
  | Dir.W => Dir.N
-- #eval Dir.E.turn

/-
lemma turn_four_times_eq_self : ∀ d : Dir, d.turn.turn.turn.turn = d := by
  intro d
  dsimp [turn]
  cases d <;> simp
-/

end Dir

/-- 2D vector: `Int × Int` -/
abbrev Vec₂ := Int × Int

instance : Inhabited Vec₂ where default := (0, 0)
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

/-- One of definitions of LT on Vec₂ -/
instance : LT Vec₂ where
  lt (a b : Vec₂) := a.1 < b.1 ∧ a.2 < b.2

instance instDecidableLtVec₂ (a b : Vec₂) : Decidable (a < b) := by
  simp [LT.lt]
  have s1 : Decidable (a.fst < b.fst) := by exact a.fst.decLt b.fst
  have s1 : Decidable (a.snd < b.snd) := by exact a.snd.decLt b.snd
  exact instDecidableAnd

#guard ((0, 0) : Vec₂) < ((8, 2) : Vec₂)

instance : LE Vec₂ where
  le (a b : Vec₂) := a.1 ≤ b.1 ∧ a.2 ≤ b.2

instance instDecidableLeVec₂ (a b : Vec₂) : Decidable (a ≤ b) := by
  simp [LE.le]
  have s1 : Decidable (a.fst ≤ b.fst) := by exact a.fst.decLe b.fst
  have s1 : Decidable (a.snd ≤ b.snd) := by exact a.snd.decLe b.snd
  exact instDecidableAnd

#guard ((0, 0) : Vec₂) ≤ ((8, 2) : Vec₂)

/-- return `(0, 0) ≤ pos ∧ ≤ size` -/
def geZeroAndLe (size pos : Vec₂) : Bool := (0, 0) ≤ pos && pos ≤ size

/-- glyph ≤₀ for geZeroAndLe: `(0, 0) ≤ pos ∧ ≤ size` -/
syntax:50 term:51 " ≤₀ " term:50 : term
macro_rules | `($a ≤₀ $b) => `(geZeroAndLe $b $a)

/-- return `(0, 0) ≤ pos ∧ < size` -/
def geZeroAndLt (size pos : Vec₂) : Bool := (0, 0) ≤ pos && pos < size

/-- glyph <₀ for geZeroAndLt -/
syntax:50 (name := syntaxInfixGeZeroAndLt) term:51 " <₀ " term:50 : term
macro_rules | `($a <₀ $b) => `(geZeroAndLt $b $a)

-- #eval ((0, 0) : Vec₂) < (3, 2)
-- #eval geZeroAndLt (5, 5) (3, 2)
-- #eval (3, 2) <₀ (5, 5)

-- def Vec₂.toUInt64 (v : Vec₂) : (UInt64 × UInt64) := (v.1.toUInt64, v.2.toUInt64)

namespace Dir

/-- return the corresponding `Dir2` -/
def asVec₂ : Dir → Vec₂
  | Dir.N => (-1,  0)
  | Dir.E => ( 0,  1)
  | Dir.S => ( 1,  0)
  | Dir.W => ( 0, -1)
-- #eval (8, 5) + Dir.N.asVec₂

instance incetanceDirAdd : HAdd Dir Dir Vec₂ where
  hAdd a b := asVec₂ a + asVec₂ b

instance incetanceDirSub : HSub Dir Dir Vec₂ where
  hSub a b := asVec₂ a - asVec₂ b

instance : HAdd Vec₂ Dir Vec₂ where
  hAdd (v : Vec₂) (d : Dir) : Vec₂ :=
    let vd := d.asVec₂
    (v.1 + vd.1, v.2 + vd.2)

instance : HAdd (Nat × Nat) Dir (Option (Nat × Nat)) where
  hAdd (v : Nat × Nat) (d : Dir) : (Option (Nat × Nat)) :=
    let dv := d.asVec₂
    let (y, x) := (v.1.toInt64.toInt + dv.1, v.2.toInt64.toInt + dv.2)
    if let some y := y.toNat? then
      if let some x := x.toNat? then some (y, x) else none
    else none

/-- 8 neighbors -/
def eightNeighbors : Array Vec₂ := #[
  Dir.N.asVec₂,
  Dir.E.asVec₂,
  Dir.S.asVec₂,
  Dir.W.asVec₂,
  Dir.N + Dir.E,
  Dir.E + Dir.S,
  Dir.S + Dir.W,
  Dir.W + Dir.N,
]

end Dir

/-- `Vec₂` of `Nat` version as valid index for `Rect`. -/
abbrev Idx₂ := Nat × Nat

-- instance : ToString Idx₂ where toString v := toString v.val

instance : Coe (Nat × Nat) Idx₂ where
  coe v := v -- (v.1, v.2)

instance : Coe Idx₂ Vec₂ where
  coe v := (((↑ v.1) : Int), ((↑ v.2) : Int))

instance : Coe Vec₂ (Option Idx₂) where
  coe v := if (0, 0) ≤ v then some (v.fst.toNat, v.snd.toNat) else none

-- def v : Vec₂ := (1, 1)
-- def v : Idx₂ := (1, 1)
-- def d : Idx₂ := ⟨(1, 1), by exact ⟨rfl, rfl⟩⟩
-- #check ((↑ d) : Vec₂)
-- #check ((↑ d) : Idx₂)
-- def w : Vec₂ := (-1, -1)
-- #eval (↑ w)
instance inhabitedIdx₂ : Inhabited Idx₂ where default := ((0 : Nat), (0 : Nat))

-- namespace Idx₂

instance : HAdd Idx₂ Vec₂ Vec₂ where
  hAdd (v : Idx₂) (d : Vec₂) : Vec₂ := (↑ v : Vec₂) + d

#guard ((1, 2) : Idx₂) + ((-2, -3) : Vec₂) == ((-1, -1) : Vec₂)

instance : HAdd Idx₂ Vec₂ (Option Idx₂) where
  hAdd (v : Idx₂) (d : Vec₂) : (Option Idx₂) := ↑ (v + d)

#guard (↑ (((1, 2) : Idx₂) + ((-2, -3) : Vec₂)) : Option Idx₂) == none

instance : HAdd Idx₂ Dir (Option Idx₂) where
  hAdd (v : Idx₂) (d : Dir) : (Option Idx₂) := (↑ v : Vec₂) + d

#guard (default : Idx₂) + Dir.W == none

-- /-- class for indices for `Rect` -/
-- class RectIndex (α : Type) where
--   /-- return a pair of indices for `Rect` -/
--   toIndex₂ : α → Idx₂
--
-- instance : RectIndex Idx₂ where
--   toIndex₂ p := p
--
-- /-- class for optional indices for `Rect` -/
-- class RectIndexMaybe (α : Type) where
--   /-- return an optional pair of indices for `Rect` -/
--   toIndex₂? : α → Option (Nat × Nat)
--
-- instance : RectIndexMaybe Vec₂ where
--   toIndex₂? p := if (0, 0) ≤ p then some (p.1.toNat, p.2.toNat) else none
--
-- instance : RectIndexMaybe Idx₂ where
--   toIndex₂? p := some (↑ p)
--
-- instance : RectIndexMaybe (Nat × Nat) where
--   toIndex₂? p := some p
--
-- #check RectIndex.toIndex₂ ((↑ d) : Idx₂)

-- /-- return the list of `(0 : UInt64)` to `n` -/
-- partial
-- def range_list (n : Int) : List Int := List.range n.toNat |>.map Int.ofNat

/-- return all valid indices smaller than `p`

  Example:
  toList' (3, 2) = [(0,0), (0,1), (1,0), (1,1), (2,0), (2,1)]
-/
def toList' (p : Idx₂) : List Idx₂ :=
  List.map (fun y ↦ (List.range p.2).map (y, ·) ) (List.range p.1) |>.flatten

#guard toList' (3, 2) = [(0,0), (0,1), (1,0), (1,1), (2,0), (2,1)]

open Std.HashMap

variable {α : Type}

/--
### A Presentation of bounded 2D spaces

Note: this implementation accept zero space for now.
And It returns the `default` by `·.get (0, 0)`
-/
structure Rect (α : Type) [BEq α] where
  /-- width -/
  width : Nat
  /-- internal data storage -/
  vector : Array α
deriving Hashable --, Repr

instance [BEq α] : BEq (Rect α) where
  beq a b := a.width == b.width && a.vector == b.vector

/-- Split a list into consecutive chunks of length `n` (the last chunk may be shorter). -/
def fold_n (n : Nat) (l : List α) (h : 0 < n) : List (List α) :=
  if l.length = 0 then
    ([] : List (List α))
  else
    if n < l.length then
      (l.take n) :: fold_n n (l.drop n) h
    else
      ([l] : List (List α))

-- #eval fold_n 3 #[0, 2, 3, 10, 12, 19, 20, 22, 23].toList (by simp)

/-- return `self` as `List (List α)` -/
def Rect.to2Dmatrix {α : Type} [BEq α] (self : Rect α) : List (List α) :=
  let w : Nat := self.width
  if h : 0 < w then fold_n w self.vector.toList h else []

#guard (Rect.mk 2 #[1, 2, 3, 4]).to2Dmatrix.toString == "[[1, 2], [3, 4]]"

instance [ToString α] [BEq α] : ToString (Rect α) where
  toString self :=
    let ll := self.to2Dmatrix
    ll.map (fun l ↦ s!"{toString l}\n") |> String.join |> (String.append "\n" ·)

namespace Rect

/-- return the height of `Rect` -/
@[inline]
def height [BEq α] (self : Rect α) : Nat := self.vector.size / self.width

/-- return the pair of the height and the width of `Rect` -/
@[inline]
def geometory [BEq α] (self : Rect α) : Nat × Nat := (self.height, self.width)

/-- return a new instance fitting to the given Dim2 -/
def ofDim2 [BEq α] (h w : Nat) (default : α) : Rect α :=
  Rect.mk w (Array.replicate (h * w) default)

/-- return a new instance of Rect by converting from an 2D array -/
def of2DMatrix [BEq α] (a : Array (Array α)) : Rect α :=
  have h := a.size
  match h with
  | 0 => Rect.mk 0 #[]
  | _ =>
    let total : Nat := a.foldl (fun acc vec ↦ acc + vec.size) 0
    let w := total / h
    let v : Array α := a.foldl Array.append #[]
    Rect.mk w v

/-- return the `(i,j)`-th element of `Rect` -/
@[inline]
def rectGetElem? [BEq α] [Coe β (Option Idx₂)] (self : Rect α) (p : β) : Option α :=
  match ((↑ p) : Option Idx₂) with
  | some i => if i.snd < self.width then self.vector[self.width * i.1 + i.2]? else none
  | none   => none

/-- return the `(i,j)`-th element of `Rect` by using `[]!` -/
@[inline]
def rectGetElem! [BEq α] [Inhabited α] [Coe β (Option Idx₂)] (self : Rect α) (p : β) : α :=
  match ((↑ p) : Option Idx₂) with
    | some i => self.vector[(self.width * i.1 + i.2)]!
    | none   => self.vector[0]!

instance Rect.hasGetElem? [BEq α] [Inhabited α] [Coe β (Option Idx₂)] :
    GetElem? (Rect α) β α
        (fun col idx ↦ match ((↑ idx) : Option Idx₂) with | some i => i.fst * col.width + i.snd < col.vector.size | none => false) where
  getElem c i _ := rectGetElem! c i
  getElem? := rectGetElem?

#guard (Rect.of2DMatrix #[#[1], #[2], #[3], #[4]])[((1,0) : Vec₂)]? == some 2
#guard (Rect.of2DMatrix #[#[1], #[2], #[3], #[4]])[((1,0) : Vec₂)]! == 2
#guard (Rect.of2DMatrix #[#[1], #[2], #[3], #[4]])[((1,0) : Idx₂)]! == 2

/-- return true if `p` is a valid index of `self` -/
def validIndex? [BEq α] [Coe β (Option Idx₂)] (self : Rect α) (p : β) : Bool :=
  match ((↑ p) : Option Idx₂) with
  | some i => i.2 < self.width && (self.width * i.1 + i.2) < self.vector.size
  | _      => false

#guard (Rect.of2DMatrix #[#[1,2], #[3,6], #[9, 0]]).validIndex? ((1, 1) : Idx₂) == true
#guard (Rect.of2DMatrix #[#[1,2], #[3,6], #[9, 0]]).validIndex? ((2, 1) : Vec₂) == true
#guard (Rect.of2DMatrix #[#[1,2], #[3,6], #[9, 0]]).validIndex? (1, 2) == false
#guard (Rect.of2DMatrix #[#[1,2], #[3,6], #[9, 0]]).validIndex? (1, 3) == false
#guard (Rect.of2DMatrix #[#[1], #[2], #[3], #[4]]).validIndex? (3, 0) == true
#guard (Rect.of2DMatrix #[#[1], #[2], #[3], #[4]]).validIndex? ((-3, 0) : Vec₂) == false

-- /-- return `self[p]` as `Option` -/
-- @[inline]
-- def get? [BEq α] [RectIndexMaybe β] (self : Rect α) (p : β) : Option α :=
--   match RectIndexMaybe.toIndex₂? p with
--   | some i => if i.snd < self.width then self.vector[self.width * i.1 + i.2]? else none
--   | none => none

/-- set the `(i,j)`-th element to `val` and return the modified Mat1 instance -/
@[inline]
def set [BEq α] [Coe β (Option Idx₂)] (self : Rect α) (p : β) (val : α) : Rect α :=
  match ((↑ p) : Option Idx₂) with
  | some i =>
    let j := self.width * i.1 + i.2
    if j < self.vector.size then Rect.mk self.width (self.vector.set! j val) else self
  | none   => self

/-- modify the `(i,j)`-th element to `val` and return the modified Mat1 instance -/
@[inline]
def modify [BEq α] [Coe β (Option Idx₂)] (self : Rect α) (p: β) (f : α → α) : Rect α :=
  match ((↑ p) : Option Idx₂) with
  | some i =>
    let j := self.width * i.1 + i.2
    if j < self.vector.size then Rect.mk self.width (self.vector.modify j f) else self
    | none => self

/-- swap `self[p]` and `self[q]` -/
@[inline]
def swap [BEq α] [Coe β (Option Idx₂)] [Coe γ (Option Idx₂)]
    (self : Rect α) (p : β) (q : γ) : Rect α :=
  match ((↑ p) : Option Idx₂), ((↑ q) : Option Idx₂) with
  | some p', some q' =>
    let i : Nat := self.width * p'.fst + p'.snd
    let j : Nat := self.width * q'.fst + q'.snd
    { self with vector := Array.swapIfInBounds self.vector i j }
  | _      , _       => self

-- def r := Rect.of2DMatrix #[#[0,1], #[2,4]]
-- #eval r
-- #eval r.set (Dim2.mk 1 1) 100
-- #eval r.modify (Dim2.mk 1 1) (· + 20) 0
-- #eval r.get (Dim2.mk 0 0) 77
-- #eval r.get (Dim2.mk 1 1) 88
-- #eval r.swap (Dim2.mk 0 0) (Dim2.mk 1 1)

/-- search an element that satisfies the predicate and return indices or none -/
def findPosition? [BEq α] (r : Rect α) (f : α → Bool) : Option Idx₂ :=
  r.vector.findIdx? f |>.map (fun i ↦ (i / r.width, i % r.width))

/-- helper: search `sa` backwards from `limit` (stepping by `sub1`) for the first element satisfying `pred`. -/
partial
def findIdxOnSubarray [BEq α]
    (sa : Subarray α) (limit : Fin sa.size) (sub1 : Fin sa.size) (pred : α → Bool)
    : Option Nat :=
  if pred (sa.get limit)
  then some limit
  else
    match (limit : Nat) with
    | 0 => none
    | _ => findIdxOnSubarray sa (limit.sub sub1) sub1 pred

/-- search an element in a specific row -/
def findIdxInRow? [BEq α] (p : Rect α) (i : Nat) (pred : α → Bool) : Option (Nat × Nat) :=
  let f := i * p.width
  let t := (i + 1) * p.width
  let sa := p.vector.toSubarray f t
  if h : sa.size ≠ 0 then
    have : NeZero sa.size := by simp [neZero_iff, h]
    findIdxOnSubarray sa (Fin.ofNat sa.size (t - f - 1)) (Fin.ofNat sa.size 1) pred
      |>.map (i, ·)
  else
    none

-- #eval if let some y := Mat1.of2DMatrix #[#[1,2,3], #[4,5,6]] then y.findIdxInRow? 1 (· == 4) else none

/-- map on `Rect` -/
def map {β : Type} [BEq α] [BEq β] (self : Rect α) (f : α → β) : Rect β :=
  { self with vector := self.vector.map f }

/-- foldl on `Rect` -/
def foldl {β : Type} [BEq α] (self : Rect α) (f : β → α → β) (init : β) : β :=
  self.vector.foldl f init

/-- foldl on each row and return the results as an `Array` -/
def foldlRows {β : Type} [BEq α]
    (self : Rect α) (f : β → α → β) (init : β) : Array β :=
  Array.range self.width
    |>.map (fun i => self.vector.toSubarray i (i + self.width) |> Array.ofSubarray |>.foldl f init)

/-- map on each row -/
def mapRows {β : Type} [BEq α]
    (self : Rect α) (f : Array α → β) :  Array β :=
  Array.range (self.vector.size / self.width)
    |> .map (fun i => self.vector.toSubarray i (i + self.width) |> Array.ofSubarray |> f)

/-- return `i`-th row of `self` as a `Subarray` -/
def row [BEq α] (self : Rect α) (i : Nat) : Subarray α :=
  let j : Nat := i % (self.vector.size % self.width)
  let f : Nat := j * self.width
  let t := f + self.width
  self.vector.toSubarray f t

/-- return `j`-th column of `self` as a Array -/
def column [BEq α] [Inhabited α] (self : Rect α) (j : Nat) : Array α :=
  Array.range (self.vector.size / self.width) |>.map (fun i ↦ self[(i, j)]!)

/-- return the height and the width of `self` -/
def area [BEq α] (self : Rect α) : Nat := self.vector.size

-- @[inline] def index (size : Pos) (p : Pos) : Nat := p.fst * size.snd + p.snd

/-- return the index for `n`-th element of `self` -/
@[inline]
def toIndex? {α : Type} [BEq α] [Coe β (Option Idx₂)] (frame : Rect α) (p : β) : Option Nat :=
  match ((↑ p) : Option Idx₂) with
  | some i' =>
    let i := frame.width * i'.fst + i'.snd
    if i < frame.vector.size then some i else none
  | none    => none

-- @[inline] def index' (size : Pos) (n: Nat) : Pos := (n / size.snd, n % size.snd)

/-- return the index for the 1D vector converted from `self` -/
@[inline]
def ofIndex₁ {α : Type} [BEq α] (frame : Rect α) (n : Nat) : Nat × Nat :=
  (n / frame.width, n % frame.width)

/-- enumerate on `Rect` -/
@[inline]
def enum {α : Type} [Inhabited α] [BEq α] (self : Rect α) : Array ((Nat × Nat) × α) :=
  Array.range self.vector.size
    |>.filterMap (fun i ↦
        let p := self.ofIndex₁ i
        if let some val := self[p]? then some (p, val) else none)

/-- return the array of valid (height, width) pair of `Rect` -/
@[inline]
def range {α : Type} [BEq α] (self : Rect α) : Array (Nat × Nat) :=
  Array.range self.vector.size |>.map (fun i ↦ self.ofIndex₁ i)

-- def v := #[true, false, true, false]
-- def x := Rect.mk 2 v
-- def y := Rect.of2DMatrix #[#[(1 : Int), 2, 3], #[4, 5, 6]]
-- #eval y.range
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
