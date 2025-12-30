module

public import Lean
public import Std.Data.Iterators.Combinators.Zip

@[expose] public section

open Std Std.Iterators Std.Iterators.Iter

universe w

/-- Convert an iterator to enumerated iterator -/
@[inline]
def Std.Iterators.Iter.enumerate {α β : Type} [Iterator α Id β] [IteratorLoop α Id Id] [Finite α Id]
    (it : Iter (α := α) β) : Iter (α := Zip (Rxo.Iterator Nat) Id α β) (Nat × β) :=
  (0...it.count).iter.zip it

-- #eval [1, 4, 66].iter.enumerate.toArray
-- #eval #[1, 4, 66].iter.enumerate.toArray

/-- sum on iterator -/
@[inline]
def Std.Iterators.Iter.sum {α : Type} [Iterator α Id Nat] [IteratorLoop α Id Id]
    (it : Iter (α := α) Nat) : Nat :=
  it.fold (· + ·) 0

-- #eval [1, 4, 66].iter.sum

/-- product on iterator -/
@[inline]
def Std.Iterators.Iter.product {α : Type} [Iterator α Id Nat] [IteratorLoop α Id Id]
    (it : Iter (α := α) Nat) : Nat :=
  it.fold (· * ·) 1
-- #eval [2, 3, 6].iter.product

/-- return a HashMap over an iterator -/
@[inline]
def Std.Iterators.Iter.toHashMap {α β γ : Type} [BEq β] [Hashable β] [Iterator α Id (β × γ)] [IteratorLoop α Id Id]
    (it : Iter (α := α) (β × γ)) : HashMap β γ :=
  it.fold (fun acc pair ↦ acc.insert pair.fst pair.snd) (HashMap.emptyWithCapacity it.count)
-- #eval [(2, "aaa"), (3, "three"), (6, "six")].iter.toHashMap

/-- return a HashSet over an iterator -/
@[inline]
def Std.Iterators.Iter.toHashSet {α β : Type} [BEq β] [Hashable β] [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter (α := α) β) : HashSet β :=
  it.fold (·.insert ·) (HashSet.emptyWithCapacity it.count)
-- #eval [2, 3, 6].iter.toHashSet

