import LebFast.Heur

/-!
# The float model of the leaf check (untrusted proposal code)

A port of `gen/leafbound.py` and of the search's leaf evaluation: from a box it builds the witness fan (heuristic at
the box centre), chooses the fan centre, drops witnesses whose fan rows fail, checks the winding certificate, and
chooses `β` (identity multiplier) and `σ` (diagonal shift) for the exact check. Floats only; nothing is trusted.
-/

namespace LebesgueCover.Fast

abbrev FV := Array Float
abbrev FM := Array (Array Float)

def fzeros (n : Nat) : FV := Array.replicate n 0.0
def fmzeros (n : Nat) : FM := Array.replicate n (fzeros n)
def det2F (a b : Float × Float) : Float := a.1 * b.2 - a.2 * b.1
def uF (s : Float) : Float × Float := let d := 1.0 + s * s; ((1.0 - s * s) / d, 2.0 * s / d)
def rotF (M q : Float × Float) : Float × Float := (M.1 * q.1 - M.2 * q.2, M.2 * q.1 + M.1 * q.2)
def fmax (a b : Float) : Float := if a > b then a else b
def fmin (a b : Float) : Float := if a < b then a else b

/-- y-index layout: body 1 → (Δtx, Δty) at (0, 1); body i ≥ 2 → (Δtx, Δty, C, S) at 4i−6 .. 4i−3. -/
def yIdx (i : Nat) : Nat × Nat × Nat × Nat :=
  if i == 1 then (0, 1, 0, 0) else (4 * i - 6, 4 * i - 5, 4 * i - 4, 4 * i - 3)
/-- box coordinates of body i: (s, tx, ty) (s unused for body 1). -/
def pIdx (i : Nat) : Nat × Nat × Nat := if i == 1 then (0, 0, 1) else (3 * i - 4, 3 * i - 3, 3 * i - 2)

structure FLeaf where
  k : Nat
  nv : Nat
  c : FV
  h : FV
  M : Array (Float × Float)     -- index 0..k
  t : Array (Float × Float)
  y0 : FV
  w : FV
deriving Inhabited

def mkLeaf (k : Nat) (lo hi : FV) : FLeaf := Id.run do
  let nv := 4 * k - 2
  let c := (Array.range lo.size).map fun a => 0.5 * (lo[a]! + hi[a]!)
  let h := (Array.range lo.size).map fun a => 0.5 * (hi[a]! - lo[a]!)
  let mut M : Array (Float × Float) := #[(1.0, 0.0)]
  let mut t : Array (Float × Float) := #[(0.0, 0.0)]
  let mut y0 := fzeros nv; let mut w := fzeros nv
  for i in [1:k + 1] do
    let (si, tx, ty) := pIdx i
    let (a, b, cc, ss) := yIdx i
    t := t.push (c[tx]!, c[ty]!)
    w := (w.set! a h[tx]!).set! b h[ty]!
    if i == 1 then M := M.push (1.0, 0.0)
    else
      let sl := lo[si]!; let sh := hi[si]!
      let sm := 0.5 * (sl + sh)
      let Mi := uF sm
      let mut Cmax := 0.0; let mut Smax := 0.0
      for s in [sl, sh] do
        let us := uF s
        Cmax := fmax Cmax (1.0 - (Mi.1 * us.1 + Mi.2 * us.2))
        Smax := fmax Smax (Float.abs (det2F Mi us))
      M := M.push Mi
      y0 := y0.set! cc (-0.5 * Cmax); w := (w.set! cc (0.5 * Cmax)).set! ss Smax
  return { k, nv, c, h, M, t, y0, w }

/-- Rotation angle of body i at the centre (for the heuristic). -/
def FLeaf.rho (L : FLeaf) (i : Nat) : Float := Float.atan2 L.M[i]!.2 L.M[i]!.1

/-- x = X0 + Σ_a y_a L_a for a witness: (X0, nonzero columns as (index, vector)). -/
def linW (L : FLeaf) (i : Nat) (q : Float × Float) : (Float × Float) × Array (Nat × (Float × Float)) :=
  if i == 0 then (q, #[])
  else
    let a := rotF L.M[i]! q
    let X0 := (a.1 + L.t[i]!.1, a.2 + L.t[i]!.2)
    let (ia, ib, cc, ss) := yIdx i
    if i == 1 then (X0, #[(ia, (1.0, 0.0)), (ib, (0.0, 1.0))])
    else (X0, #[(ia, (1.0, 0.0)), (ib, (0.0, 1.0)), (cc, a), (ss, (-a.2, a.1))])

/-- dense columns of L. -/
def denseL (nv : Nat) (cols : Array (Nat × (Float × Float))) : Array (Float × Float) :=
  cols.foldl (fun acc (j, v) => acc.set! j v) (Array.replicate nv (0.0, 0.0))

/-- float fan rows: lower bound of det(x_j − z, x_{j+1} − z) on the box, per consecutive pair. -/
def fanRowsF (L : FLeaf) (ib : Array Nat) (Q : Array (Float × Float)) (z : Float × Float) : FV := Id.run do
  let m := ib.size; let nv := L.nv
  let lins := (Array.range m).map fun j => linW L ib[j]! Q[j]!
  let mut out := fzeros m
  for j in [0:m] do
    let (X, cs) := lins[j]!; let (X2, cs2) := lins[(j + 1) % m]!
    let P := (X.1 - z.1, X.2 - z.2); let P2 := (X2.1 - z.1, X2.2 - z.2)
    let Ld := denseL nv cs; let Ld2 := denseL nv cs2
    let c0 := det2F P P2
    let mut val := c0; let mut lin := 0.0; let mut quad := 0.0
    let g := (Array.range nv).map fun n => det2F P Ld2[n]! + det2F Ld[n]! P2
    for n in [0:nv] do val := val + g[n]! * L.y0[n]!
    for n in [0:nv] do
      for kk in [0:nv] do
        let A := det2F Ld[n]! Ld2[kk]!
        val := val + A * L.y0[n]! * L.y0[kk]!
        quad := quad + Float.abs A * L.w[n]! * L.w[kk]!
    for n in [0:nv] do
      let mut gy := g[n]!
      for kk in [0:nv] do gy := gy + (det2F Ld[n]! Ld2[kk]! + det2F Ld[kk]! Ld2[n]!) * L.y0[kk]!
      lin := lin + Float.abs gy * L.w[n]!
    out := out.set! j (val - lin - quad)
  return out

/-- fan centres tried. -/
def ZS : Array (Float × Float) :=
  #[(0.0, 0.0)] ++ (Array.range 8).map fun a => (0.12 * Float.cos (a.toFloat * piF / 4.0), 0.12 * Float.sin (a.toFloat * piF / 4.0))

/-- cheap norm-based row bounds for several centres (choice of z and first drop loop only). -/
def pairLbsCheap (L : FLeaf) (ib : Array Nat) (Q : Array (Float × Float)) (zs : Array (Float × Float)) : Array FV := Id.run do
  let k := L.k; let m := ib.size
  let mut aR := fzeros (k + 1); let mut dt := fzeros (k + 1)
  for i in [1:k + 1] do
    let (aa, bb, cc, ss) := yIdx i
    dt := dt.set! i (Float.sqrt (L.w[aa]! * L.w[aa]! + L.w[bb]! * L.w[bb]!))
    if i != 1 then aR := aR.set! i (Float.sqrt (L.w[ss]! * L.w[ss]! + (2.0 * L.w[cc]!) * (2.0 * L.w[cc]!)))
  let X0 := (Array.range m).map fun j => (linW L ib[j]! Q[j]!).1
  let nrm (p : Float × Float) := Float.sqrt (p.1 * p.1 + p.2 * p.2)
  let mut res : Array FV := #[]
  for z in zs do
    let mut row := fzeros m
    for j in [0:m] do
      let j2 := (j + 1) % m
      let i := ib[j]!; let i2 := ib[j2]!
      let A := (X0[j]!.1 - z.1, X0[j]!.2 - z.2); let B := (X0[j2]!.1 - z.1, X0[j2]!.2 - z.2)
      let d0 := det2F A B
      let nq := nrm Q[j]!; let nq2 := nrm Q[j2]!
      let dX := nq * aR[i]! + dt[i]!; let dX2 := nq2 * aR[i2]! + dt[i2]!
      let wq := nrm (Q[j2]!.1 - Q[j]!.1, Q[j2]!.2 - Q[j]!.2)
      let tz := nrm (L.t[i]!.1 - z.1, L.t[i]!.2 - z.2)
      let vs := wq * (dt[i]! * (1.0 + aR[i]!) + tz * aR[i]!)
      let vt := dX * (nrm B + dX2) + nrm A * dX2
      row := row.set! j (d0 - 1.05 * (if i == i2 then vs else vt))
    res := res.push row
  return res

/-- drop, for every bad row j (non-adjacent greedy), witness j+1 (or j if j+1 is a disk witness). -/
def dropBad (ib : Array Nat) (Q : Array (Float × Float)) (rows : FV) : Array Nat × Array (Float × Float) := Id.run do
  let m := ib.size
  let mut drop := Array.replicate m false
  for j in [0:m] do
    if rows[j]! ≤ 1e-13 then
      let j2 := (j + 1) % m
      let dr := if ib[j2]! != 0 then j2 else j
      if !(drop[dr]! || drop[(dr + m - 1) % m]! || drop[(dr + 1) % m]!) then drop := drop.set! dr true
  let mut ib2 : Array Nat := #[]; let mut Q2 : Array (Float × Float) := #[]
  for j in [0:m] do
    if !drop[j]! then ib2 := ib2.push ib[j]!; Q2 := Q2.push Q[j]!
  return (ib2, Q2)

def anyBad (rows : FV) : Bool := rows.any (· ≤ 1e-13)

/-- winding certificate at the centre (float). -/
def windingOkF (L : FLeaf) (ib : Array Nat) (Q : Array (Float × Float)) (z : Float × Float) : Bool := Id.run do
  let m := ib.size
  let X := (Array.range m).map fun j => let x := (linW L ib[j]! Q[j]!).1; (x.1 - z.1, x.2 - z.2)
  let mut tot := 0.0
  for j in [0:m] do
    let a := X[j]!; let b := X[(j + 1) % m]!
    let d := det2F a b; let dt := a.1 * b.1 + a.2 * b.2
    if d ≤ 0.0 then return false
    tot := tot + (if dt > 0.0 then fmin (d / dt) (0.5 * 3.1416) else fmin 3.1416 (0.5 * 3.1416 - dt / d))
  return tot < 4.0 * 3.1415 - 1e-9

/-- fan area quadratic: F0, g, H (dense) and D_i (coefficient sums for the identity term). -/
def fanQuadF (L : FLeaf) (ib : Array Nat) (Q : Array (Float × Float)) : Float × FV × FM × FV := Id.run do
  let m := ib.size; let nv := L.nv
  let lins := (Array.range m).map fun j => linW L ib[j]! Q[j]!
  let mut F0 := 0.0; let mut g := fzeros nv; let mut H := fmzeros nv; let mut D := fzeros (L.k + 1)
  for j in [0:m] do
    let j2 := (j + 1) % m
    let (X, cs) := lins[j]!; let (X2, cs2) := lins[j2]!
    F0 := F0 + 0.5 * det2F X X2
    for (n, v) in cs2 do g := g.set! n (g[n]! + 0.5 * det2F X v)
    for (n, v) in cs do g := g.set! n (g[n]! + 0.5 * det2F v X2)
    for (n, v) in cs do
      for (kk, v2) in cs2 do
        let A := 0.5 * det2F v v2
        H := H.set! n (H[n]!.set! kk (H[n]![kk]! + A))
        H := H.set! kk (H[kk]!.set! n (H[kk]![n]! + A))
    if ib[j]! == ib[j2]! && ib[j]! ≥ 2 then
      let R := L.M[ib[j]!]!
      D := D.set! ib[j]! (D[ib[j]!]! + 0.5 * det2F (rotF R Q[j]!) (rotF R Q[j2]!))
  return (F0, g, H, D)

/-- smallest eigenvalue of a symmetric matrix (cyclic Jacobi). -/
def eigMin (A0 : FM) : Float := Id.run do
  let n := A0.size
  let mut A := A0
  for _ in [0:60] do
    let mut off := 0.0
    for p in [0:n] do
      for q in [p + 1:n] do off := off + A[p]![q]! * A[p]![q]!
    if off < 1e-30 then break
    for p in [0:n] do
      for q in [p + 1:n] do
        let apq := A[p]![q]!
        if Float.abs apq > 1e-300 then
          let app := A[p]![p]!; let aqq := A[q]![q]!
          let th := (aqq - app) / (2.0 * apq)
          let tt := (if th ≥ 0.0 then 1.0 else -1.0) / (Float.abs th + Float.sqrt (th * th + 1.0))
          let c := 1.0 / Float.sqrt (tt * tt + 1.0); let s := tt * c
          -- rotate rows/columns p, q
          let mut B := A
          for r in [0:n] do
            let arp := A[r]![p]!; let arq := A[r]![q]!
            B := B.set! r ((B[r]!.set! p (c * arp - s * arq)).set! q (s * arp + c * arq))
          let mut C := B
          for r in [0:n] do
            let bpr := B[p]![r]!; let bqr := B[q]![r]!
            C := C.set! p (C[p]!.set! r (c * bpr - s * bqr))
            C := C.set! q (C[q]!.set! r (s * bpr + c * bqr))
          A := C
  let mut mn := A[0]![0]!
  for i in [1:n] do mn := fmin mn A[i]![i]!
  return mn

/-- (value, scaled shift s) with Mw + diag(s) ⪰ 0 (best of a uniform and a Jacobi-scaled choice). -/
def shiftBound (Mw : FM) : Float × FV := Id.run do
  let n := Mw.size
  let lam := eigMin Mw
  let mut best := (0.5 * fmin 0.0 lam * n.toFloat, Array.replicate n (fmax 0.0 (-lam)))
  let d := (Array.range n).map fun a => Float.sqrt (fmax (Mw[a]!.foldl (fun s x => s + Float.abs x) 0.0) 1e-300)
  let Md := (Array.range n).map fun a => (Array.range n).map fun b => Mw[a]![b]! / (d[a]! * d[b]!)
  let lamd := eigMin Md
  if lamd < 0.0 then
    let s2 := (Array.range n).map fun a => -lamd * d[a]! * d[a]!
    let v := -0.5 * s2.foldl (· + ·) 0.0
    if v > best.1 then best := (v, s2)
  return best

/-- best single-fan bound with the β scan: (bound, alpha, scaled shift s). -/
def leafBoundF (L : FLeaf) (ib : Array Nat) (Q : Array (Float × Float)) : Float × Float × FV := Id.run do
  let (F0, g, H, D) := fanQuadF L ib Q
  let nv := L.nv
  let mut best : Float × Float × FV := (-1e300, 0.0, fzeros nv)
  for alpha in [0.0, 0.5, 1.0, 1.5, 2.0] do
    let mut g2 := g; let mut H2 := H
    for i in [2:L.k + 1] do
      let beta := (alpha - 1.0) * D[i]!
      let (_, _, cc, ss) := yIdx i
      g2 := g2.set! cc (g2[cc]! + 2.0 * beta)
      H2 := H2.set! cc (H2[cc]!.set! cc (H2[cc]![cc]! + 2.0 * beta))
      H2 := H2.set! ss (H2[ss]!.set! ss (H2[ss]![ss]! + 2.0 * beta))
    let mut Qy0 := F0
    for a in [0:nv] do Qy0 := Qy0 + g2[a]! * L.y0[a]!
    for a in [0:nv] do
      for b in [0:nv] do Qy0 := Qy0 + 0.5 * L.y0[a]! * H2[a]![b]! * L.y0[b]!
    let mut lin := 0.0
    for a in [0:nv] do
      let mut gy := g2[a]!
      for b in [0:nv] do gy := gy + H2[a]![b]! * L.y0[b]!
      lin := lin + Float.abs gy * L.w[a]!
    let Mw := (Array.range nv).map fun a => (Array.range nv).map fun b => L.w[a]! * H2[a]![b]! * L.w[b]!
    let (sv, s) := shiftBound Mw
    let b := Qy0 - lin + sv
    if b > best.1 then best := (b, alpha, s)
  return best

/-- A proposed fan: witnesses, centre, β per body, σ per y-variable (floats), and the float bound. -/
structure Proposal where
  ib : Array Nat
  Q : Array (Float × Float)
  z : Float × Float
  beta : FV
  sigma : FV
  bound : Float
deriving Inhabited

/-- The search's leaf evaluation (fan from the heuristic at the centre); `none` if the fan fails. -/
def proposeAt (bs : Array FBody) (L : FLeaf) (pl : FPlace) (N : Nat) (eps : Float) : Option Proposal := Id.run do
  let (ib0, Q0) := witnessesF bs pl N eps
  let shrink := 1.0 - 1.0 / 1073741824.0
  let Q0 := Q0.map fun (x, y) => (x * shrink, y * shrink)
  let lbs := pairLbsCheap L ib0 Q0 ZS
  let mut zi := 0; let mut nb := ib0.size + 1
  for i in [0:ZS.size] do
    let c := (lbs[i]!.filter (· ≤ 1e-13)).size
    if c < nb then nb := c; zi := i
  let z := ZS[zi]!
  let mut ib := ib0; let mut Q := Q0
  for _ in [0:100] do
    let rows := (pairLbsCheap L ib Q #[z])[0]!
    if !anyBad rows || ib.size ≤ 4 then break
    (ib, Q) := dropBad ib Q rows
  let mut rows := fanRowsF L ib Q z
  for _ in [0:100] do
    rows := fanRowsF L ib Q z
    if !anyBad rows || ib.size ≤ 4 then break
    (ib, Q) := dropBad ib Q rows
  if ib.size < 3 || anyBad rows || !windingOkF L ib Q z then return none
  let (b, alpha, s) := leafBoundF L ib Q
  let (_, _, _, D) := fanQuadF L ib Q
  let beta := (Array.range (L.k + 1)).map fun i => if i ≥ 2 then (alpha - 1.0) * D[i]! else 0.0
  let sigma := (Array.range L.nv).map fun a => if L.w[a]! > 0.0 then s[a]! / (L.w[a]! * L.w[a]!) else 0.0
  return some { ib, Q, z, beta, sigma, bound := b }

/-- The centre placement for the heuristic. -/
def centrePlace (L : FLeaf) : FPlace := Id.run do
  let mut pl : FPlace := #[(0.0, (0.0, 0.0))]
  for i in [1:L.k + 1] do
    pl := pl.push ((if i == 1 then 0.0 else L.rho i), L.t[i]!)
  return pl

end LebesgueCover.Fast
