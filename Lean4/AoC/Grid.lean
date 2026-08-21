module

public meta import Std.Data.Iterators.Producers.Vector
public import Std.Data.Iterators

@[expose] public section

namespace Grid

universe u
variable {α β γ : Type u}

/-- 2D matrix of inhabited α, indexed by `Nat × Nat`.
- `new (height width : Nat) (init : α) : Grid α height width`
- `grid[(h, w)]? : Option α`
- `grid[(h, w)]! : α`
- `set (g : Grid α h w) (value: α) : Grid α h w`
-/
structure Grid (α : Type u) [Inhabited α] (h w : Nat) where
  vector : Vector (Vector α w) h
deriving BEq, Repr

def Grid.new [Inhabited α] (h w : Nat) (a : α := default) : Grid α h w :=
  Grid.mk <| Vector.replicate h (Vector.replicate w a)

instance Grid.isGetElem [Inhabited α] {h w : Nat} :
    GetElem? (Grid α h w) (Nat × Nat) α (fun _ i ↦ i.fst < h && i.snd < w) where
  getElem? self i := self.vector[i.fst]? >>= (·[i.snd]?)
  getElem self i _ := self.vector[i.fst]![i.snd]!

@[inline]
def Grid.set [Inhabited α] {h w : Nat}
    (grid : @&Grid α h w) (i : Nat × Nat) (x : α) : Grid α h w :=
  Grid.mk <| grid.vector.set! i.fst (grid.vector[i.fst]!.set! i.snd x)

#guard (Grid.new 3 2 false)[(4,1)]? == none
#guard (Grid.new 3 2 false)[(1,1)]! == false
#guard Grid.new 3 2 false |>.set (1, 0) true |> (·[(1,0)]!)

/-- Generate a new `Grid β` by mapping `f : Nat → Nat → α → β` to `Grid α`. -/
def Grid.map [Inhabited α] [Inhabited β] {h w : Nat}
    (grid : Grid α h w) (f : Nat → Nat → α → β) : Grid β h w :=
  Grid.mk <| grid.vector.mapIdx (fun i v ↦ v.mapIdx (fun j x ↦ f i j x))

#guard
  Grid.new 2 2 'A'
    |>.map (fun h w _ ↦ (h + w) % 2 == 0)
    |>.vector
    |>.map (·.iter.filter (·) |>.length)
    |>.sum
    |> (· == 2)

/-- Generate an `Iter ((Nat × Nat) × α)` from `Grid α`. -/
def Grid.enumerate [Inhabited α] {h w : Nat} (grid : Grid α h w) :=
  grid.vector.mapIdx (fun i v ↦ v.mapIdx (fun j x ↦ ((i, j), x))) |>.flatten |>.iter

#guard
  Grid.new 2 2 false
    |>.enumerate
    |>.map (fun (i, _) ↦ i.fst * 10 + i.snd) -- #[0, 1, 10, 11]
    |>.fold (· + ·) 0
    |> (· == 22)

/-- O(n) oonvert from `Array (Array α)` to a `Grid`. -/
def Grid.of2DArray {α : Type u} [Inhabited α]
    (a : Array (Array α)) (w : Nat := a[0]!.size) : Grid α a.size w := Id.run do
  let mut g := Grid.new a.size w (default : α)
  for (l, i) in a.zipIdx.iter do
    for (v, j) in l.zipIdx.iter do
      g := g.set (i, j) v
  return g

-- #eval Grid.of2DArray #[#[true], #[false]] |>.vector |>.toArray
