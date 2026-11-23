module

-- @[expose] public section

/-- Linear-interpolated quantile of a soted data -/
def quantile (data : Array Float) (p : Float) : Float :=
  let pos : Float := p * (data.size - 1).toFloat
  let lo : Nat := pos.floor.toUSize.toNat
  let hi : Nat := pos.ceil.toUSize.toNat
  let frac : Float := pos - lo.toFloat
  data[lo]! + frac * (data[hi]! - data[lo]!)

def silvermanBandwidth (data : Array Float) : Float :=
  let n : Float := data.size.toFloat
  let mean : Float := data.sum / n
  let sd : Float := data.map (· - mean |>.pow 2.0) |>.sum |> (· / (n - 1.0)) |>.sqrt
  let sorted : Array Float := data.qsort
  let iqr : Float := quantile sorted 0.75 - quantile sorted 0.25
  let spread : Float := if iqr > 0.0 then min sd (iqr / 1.34) else sd
  0.9 * spread * n ^ (-0.2)

structure Kde where
  data : Array Float
  bandwidth : Float

def Kde.new (data : Array Float) (bandwidth : Option Float) : Option Kde := Id.run do
  if data.size < 2 then return none
  if data.any (!·.isFinite) then return none
  let h : Float := match bandwidth with
    | none => silvermanBandwidth data
    | some b => b
  return if h > 0.0 && h.isFinite then some (Kde.mk data h) else none

/-- Density estimation at a  single point. O(n) -/
def Kde.pdf (self : Kde) (x : Float) : Float :=
  let inv_h : Float := 1.0 / self.bandwidth
  let sum : Float := self.data.map (fun xi ↦ let u := (x - xi) * inv_h; (-0.5 * u * u).exp) |>.sum
  sum / (self.data.size.toFloat * self.bandwidth * (2.0 * 3.141592).sqrt)

def Kde.evaluateGrid (self : Kde) (lo hi : Float) (m : Nat) : Array (Float × Float) :=
  let step : Float := (hi - lo) / (m - 1).toFloat
  (Array.range m).map (fun i ↦ let x := lo + step * i.toFloat; (x, self.pdf x))

public def kde (data : Array Float) (lo hi : Float) (m : Nat) : Array (Float × Float) :=
  match Kde.new data none with
  | none    => #[]
  | some kd => kd.evaluateGrid lo hi m

public def hist (data : Array Float) (lo hi : Float) (m : Nat) : Array (Nat × Float) := Id.run do
  let mut bands : Array Float := Array.replicate m 0.0
  let step : Float := (hi - lo) / m.toFloat
  for d in data do
    let i : UInt64 := min (max 0.0 (d / step)) (m - 1).toFloat |>.toUInt64
    bands := bands.modify i.toNat (· + 1.0)
  return bands.zipIdx.map (·.swap)

-- #eval silvermanBandwidth #[0.0, 1.0, 3.0, 1.2, 2.2]
-- #eval kde #[1.0, 1.5, 0.4, 1.2, 2.2] 0.0 3.0 3
-- #eval hist #[1.0, 1.5, 0.4, 1.2, 2.2] 0.0 3.0 3
