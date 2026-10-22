/-!
# Witness heuristic in floating point (untrusted proposal code)

A port of the float witness heuristic of the published checker (support points of the hull in `N` equally spaced
directions, then insertion of support points in the outer normal directions of the polygon's edges), run at a
placement given by translations and rotation angles. The soundness theorems quantify over all witness lists, so
nothing here needs a proof; the exact checks decide.
-/

namespace LebesgueCover.Fast

def piF : Float := 3.141592653589793

/-- A Reuleaux body: `n` and its unrotated vertices (floats). -/
structure FBody where
  n : Nat
  V : Array (Float × Float)
deriving Inhabited

def mkFBody (n : Nat) : FBody :=
  let R := 1.0 / (2.0 * Float.cos (piF / (2.0 * n.toFloat)))
  { n, V := (Array.range n).map fun l =>
      (R * Float.cos (2.0 * piF * l.toFloat / n.toFloat), R * Float.sin (2.0 * piF * l.toFloat / n.toFloat)) }

/-- `x mod 2π` in `[0, 2π)` as numpy computes it for `x ∈ (−4π, 2π)`. -/
def mod2pi (x : Float) : Float :=
  let tp := 2.0 * piF
  let m := if x ≥ tp then x - tp else if x ≤ -tp then x + tp else x
  if m < 0.0 then m + tp else m

/-- A placement: per body `0..k` the rotation angle and the translation. -/
abbrev FPlace := Array (Float × (Float × Float))

/-- Support value and point of body `i` in direction `phi` (`i = 0`: the disk of radius `1/2`). -/
def suppBody (bs : Array FBody) (pl : FPlace) (i : Nat) (phi : Float) : Float × (Float × Float) :=
  let ux := Float.cos phi; let uy := Float.sin phi
  let (rho, t) := pl[i]!
  if i == 0 then (0.5, (0.5 * ux, 0.5 * uy))
  else Id.run do
    let bd := bs[i - 1]!
    let n := bd.n
    let c := Float.cos rho; let s := Float.sin rho
    let Vr := bd.V.map fun (x, y) => (x * c - y * s, x * s + y * c)
    let proj := Vr.map fun (x, y) => ux * x + uy * y
    let mut best := proj[0]!; let mut pt := Vr[0]!
    for l in [1:n] do
      if proj[l]! > best then
        best := proj[l]!; pt := Vr[l]!
    for l in [0:n] do
      let phl := rho + 2.0 * piF * l.toFloat / n.toFloat
      let off := mod2pi (phi - (phl + piF - piF / (2.0 * n.toFloat)))
      let val := 1.0 + proj[l]!
      if off ≤ piF / n.toFloat && val > best then
        best := val; pt := (Vr[l]!.1 + ux, Vr[l]!.2 + uy)
    return (best + (ux * t.1 + uy * t.2), (pt.1 + t.1, pt.2 + t.2))

/-- Support over all bodies: (body, point, value), first maximum. -/
def supp (bs : Array FBody) (pl : FPlace) (phi : Float) : Nat × (Float × Float) × Float := Id.run do
  let (h0, p0) := suppBody bs pl 0 phi
  let mut hb := h0; let mut pb := p0; let mut ib := 0
  for i in [1:pl.size] do
    let (h, p) := suppBody bs pl i phi
    if h > hb then
      hb := h; pb := p; ib := i
  return (ib, pb, hb)

/-- The witness heuristic at a placement: body indices and body-frame points. -/
def witnessesF (bs : Array FBody) (pl : FPlace) (N : Nat) (eps : Float) : Array Nat × Array (Float × Float) := Id.run do
  let th := (Array.range N).map fun j => 2.0 * piF * j.toFloat / N.toFloat
  let S := th.map fun phi => supp bs pl phi
  -- drop consecutive duplicates (cyclic comparison with the previous point)
  let mut ib : Array Nat := #[]; let mut X : Array (Float × Float) := #[]
  for j in [0:N] do
    let (b, p, _) := S[j]!
    let (_, q, _) := S[(j + N - 1) % N]!
    let dx := Float.abs (p.1 - q.1); let dy := Float.abs (p.2 - q.2)
    if (if dx > dy then dx else dy) > 1e-14 then
      ib := ib.push b; X := X.push p
  for _ in [0:60] do
    let m := X.size
    let mut adds : Array (Nat × Nat × (Float × Float)) := #[]
    for j in [0:m] do
      let P := X[j]!; let Pn := X[(j + 1) % m]!
      let ex := Pn.1 - P.1; let ey := Pn.2 - P.2
      let nx := ey; let ny := -ex
      let ln := Float.sqrt (nx * nx + ny * ny)
      if ln > 1e-15 then
        let phi := Float.atan2 ny nx
        let (jb, Sp, hs) := supp bs pl phi
        let gap := hs - (P.1 * (nx / ln) + P.2 * (ny / ln))
        if gap > eps then adds := adds.push (j, jb, Sp)
    if adds.size == 0 then break
    -- insert in descending order of j (so earlier indices stay valid)
    let mut ib2 := ib; let mut X2 := X
    for r in [0:adds.size] do
      let (j, b, p) := adds[adds.size - 1 - r]!
      ib2 := ib2.insertIdx! (j + 1) b; X2 := X2.insertIdx! (j + 1) p
    ib := ib2; X := X2
  -- body frame
  let Q := (Array.range ib.size).map fun j =>
    let i := ib[j]!; let x := X[j]!
    if i == 0 then x
    else
      let (rho, t) := pl[i]!
      let c := Float.cos rho; let s := Float.sin rho
      let y0 := x.1 - t.1; let y1 := x.2 - t.2
      (c * y0 + s * y1, -s * y0 + c * y1)
  return (ib, Q)

end LebesgueCover.Fast
