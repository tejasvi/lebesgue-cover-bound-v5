/-!
# The fast exact leaf check (core Lean, compiled)

The same checks as the reference checker `LebesgueCover.Cert.leafOK`, organized for speed: witness data
(centre positions, rotated body-frame points) computed once; a fan row is the quadratic lower bound restricted to the
y-variables of its two bodies (the other coefficients vanish); the fan-area coefficients are sums over the cyclic
pairs whose bodies own the variables (the other terms vanish); vectors and matrices are arrays. The bridge theorem
(LebesgueCover/FastBridge.lean) proves that this check returns the reference check's value.
-/

namespace LebesgueCover.Fast

def det2Q (a b : Rat × Rat) : Rat := a.1 * b.2 - a.2 * b.1
def dot2Q (a b : Rat × Rat) : Rat := a.1 * b.1 + a.2 * b.2
def rot2Q (u q : Rat × Rat) : Rat × Rat := (u.1 * q.1 - u.2 * q.2, u.2 * q.1 + u.1 * q.2)
def J2Q (q : Rat × Rat) : Rat × Rat := (-q.2, q.1)
def cuQF (s : Rat) : Rat := (1 - s ^ 2) / (1 + s ^ 2)
def suQF (s : Rat) : Rat := 2 * s / (1 + s ^ 2)
def uQF (s : Rat) : Rat × Rat := (cuQF s, suQF s)

/-- `Σ_{a ∈ l} f a` (left fold). -/
def lsum (l : List Nat) (f : Nat → Rat) : Rat := l.foldl (fun acc a => acc + f a) 0

/-! ## Layout (as in the reference checker) -/

def yTxF (i : Nat) : Nat := if i = 1 then 0 else 4 * i - 6
def yTyF (i : Nat) : Nat := if i = 1 then 1 else 4 * i - 5
def yCF (i : Nat) : Nat := 4 * i - 4
def ySF (i : Nat) : Nat := 4 * i - 3
def bTxF (i : Nat) : Nat := if i = 1 then 0 else 3 * i - 3
def bTyF (i : Nat) : Nat := if i = 1 then 1 else 3 * i - 2
def bSF (i : Nat) : Nat := 3 * i - 4
def yBodyF (v : Nat) : Nat := if v < 2 then 1 else (v + 6) / 4
def yKindF (v : Nat) : Nat := if v < 2 then v else (v + 6) % 4

/-- y-variables of body `i`. -/
def varsOf (i : Nat) : List Nat :=
  if i = 0 then [] else if i = 1 then [0, 1] else [4 * i - 6, 4 * i - 5, 4 * i - 4, 4 * i - 3]

structure BBF where
  tc : Rat × Rat
  ht : Rat × Rat
  M : Rat × Rat
  Cmax : Rat
  Smax : Rat
  sOK : Bool
deriving Inhabited

def bodyBoxF (lo hi : Nat → Rat) (i : Nat) : BBF :=
  if i = 0 then ⟨(0, 0), (0, 0), (1, 0), 0, 0, true⟩
  else
    let tc := ((lo (bTxF i) + hi (bTxF i)) / 2, (lo (bTyF i) + hi (bTyF i)) / 2)
    let ht := ((hi (bTxF i) - lo (bTxF i)) / 2, (hi (bTyF i) - lo (bTyF i)) / 2)
    if i = 1 then ⟨tc, ht, (1, 0), 0, 0, true⟩
    else
      let sl := lo (bSF i); let sh := hi (bSF i); let m := (sl + sh) / 2
      let M := uQF m
      let Cmax := max (1 - dot2Q M (uQF sl)) (1 - dot2Q M (uQF sh))
      let Smax := max (det2Q M (uQF sl)).abs (det2Q M (uQF sh)).abs
      ⟨tc, ht, M, Cmax, Smax, decide (0 ≤ sl ∧ sl ≤ sh ∧ sh ≤ 1)⟩

def yCentreF (bb : Nat → BBF) (v : Nat) : Rat := if yKindF v = 2 then -(bb (yBodyF v)).Cmax / 2 else 0
def yHalfF (bb : Nat → BBF) (v : Nat) : Rat :=
  let B := bb (yBodyF v)
  match yKindF v with
  | 0 => B.ht.1
  | 1 => B.ht.2
  | 2 => B.Cmax / 2
  | _ => B.Smax

/-! ## Witnesses with precomputed data -/

structure FWit where
  body : Nat
  pt : Rat × Rat
  a : Rat × Rat      -- `rot2 M pt` (body ≥ 1)
  X0 : Rat × Rat     -- position at `y = 0`
deriving Inhabited

def mkFWit (bb : Nat → BBF) (body : Nat) (pt : Rat × Rat) : FWit :=
  if body = 0 then ⟨0, pt, (0, 0), pt⟩
  else
    let B := bb body
    let a := rot2Q B.M pt
    ⟨body, pt, a, (a.1 + B.tc.1, a.2 + B.tc.2)⟩

def witLF (w : FWit) (v : Nat) : Rat × Rat :=
  if w.body = 0 then (0, 0)
  else if v = yTxF w.body then (1, 0)
  else if v = yTyF w.body then (0, 1)
  else if 2 ≤ w.body ∧ v = yCF w.body then w.a
  else if 2 ≤ w.body ∧ v = ySF w.body then J2Q w.a
  else (0, 0)

def pairC0F (P0 Q0 : Rat × Rat) : Rat := det2Q P0 Q0
def pairGF (P0 Q0 : Rat × Rat) (L M : Nat → Rat × Rat) (a : Nat) : Rat := det2Q P0 (M a) + det2Q (L a) Q0
def pairAF (L M : Nat → Rat × Rat) (a b : Nat) : Rat := det2Q (L a) (M b)

/-- The quadratic lower bound restricted to the index list `S`. -/
def quadLowerAbsS (S : List Nat) (c0 : Rat) (g : Nat → Rat) (A : Nat → Nat → Rat) (y0 w : Nat → Rat) : Rat :=
  c0 + lsum S (fun a => g a * y0 a) + lsum S (fun a => lsum S (fun b => A a b * y0 a * y0 b))
    - lsum S (fun a => (g a + lsum S (fun b => (A a b + A b a) * y0 b)).abs * w a)
    - lsum S (fun a => lsum S (fun b => (A a b).abs * w a * w b))

def pairVars (w w' : FWit) : List Nat := if w.body = w'.body then varsOf w.body else varsOf w.body ++ varsOf w'.body

def fanRowF (y0 wv : Nat → Rat) (z : Rat × Rat) (w w' : FWit) : Rat :=
  let P := (w.X0.1 - z.1, w.X0.2 - z.2); let Q := (w'.X0.1 - z.1, w'.X0.2 - z.2)
  quadLowerAbsS (pairVars w w') (pairC0F P Q) (pairGF P Q (witLF w) (witLF w')) (pairAF (witLF w) (witLF w')) y0 wv

def cycPairsF {α : Type} : List α → List (α × α)
  | [] => []
  | a :: t => List.zip (a :: t) (t ++ [a])

def angleUBF (P Q : Rat × Rat) : Rat :=
  if 0 < dot2Q P Q then min (det2Q P Q / dot2Q P Q) (31416 / 20000)
  else min (31416 / 10000) (31416 / 20000 - dot2Q P Q / det2Q P Q)

def windOKF (z : Rat × Rat) (prs : List (FWit × FWit)) : Bool :=
  let ps := prs.map fun (w, w') => ((w.X0.1 - z.1, w.X0.2 - z.2), (w'.X0.1 - z.1, w'.X0.2 - z.2))
  (ps.all fun (P, Q) => decide (0 < det2Q P Q)) &&
    decide ((ps.map fun (P, Q) => angleUBF P Q).sum < 4 * (31415 / 10000))

def memOKF (ns : List Nat) (V : Nat → Nat → Rat × Rat) (ν : Rat) (w : FWit) : Bool :=
  if w.body = 0 then decide (dot2Q w.pt w.pt ≤ 1 / 4)
  else
    let n := ns.getD (w.body - 1) 0
    decide (0 < n) && (List.range n).all fun l =>
      let d := (w.pt.1 - (V n l).1, w.pt.2 - (V n l).2)
      decide (dot2Q d d ≤ (1 - ν) ^ 2)

/-! ## Fan-area coefficients -/

def fanGval (prs : List (FWit × FWit)) (β : Nat → Rat) (a : Nat) : Rat :=
  let i := yBodyF a
  ((prs.filter fun p => p.1.body = i ∨ p.2.body = i).map fun (w, w') =>
      pairGF w.X0 w'.X0 (witLF w) (witLF w') a / 2).sum +
    (if yKindF a = 2 then 2 * β (yBodyF a) else 0)

def fanHval (prs : List (FWit × FWit)) (β : Nat → Rat) (a b : Nat) : Rat :=
  let ia := yBodyF a; let ib := yBodyF b
  ((prs.filter fun p => p.1.body = ia ∧ p.2.body = ib).map fun (w, w') => pairAF (witLF w) (witLF w') a b / 2).sum +
    ((prs.filter fun p => p.1.body = ib ∧ p.2.body = ia).map fun (w, w') => pairAF (witLF w) (witLF w') b a / 2).sum +
    (if a = b ∧ (yKindF a = 2 ∨ yKindF a = 3) then 2 * β (yBodyF a) else 0)

def fanGF (nv : Nat) (prs : List (FWit × FWit)) (β : Nat → Rat) : Array Rat :=
  (Array.range nv).map fun a => fanGval prs β a

def fanHF (nv : Nat) (prs : List (FWit × FWit)) (β : Nat → Rat) : Array (Array Rat) :=
  (Array.range nv).map fun a => (Array.range nv).map fun b => fanHval prs β a b

/-! ## PSD certificate and the bound -/

def ldlF (n : Nat) (N : Nat → Nat → Rat) : Array (Array Rat) × Array Rat := Id.run do
  let mut Lm : Array (Array Rat) := Array.replicate n (Array.replicate n 0)
  let mut Dm : Array Rat := Array.replicate n 0
  for a in [0:n] do
    for b in [0:a] do
      let mut s := N a b
      for c in [0:b] do
        s := s - (Lm[a]!)[c]! * (Lm[b]!)[c]! * Dm[c]!
      let v := if Dm[b]! = 0 then 0 else s / Dm[b]!
      Lm := Lm.set! a ((Lm[a]!).set! b v)
    let mut s := N a a
    for c in [0:a] do
      s := s - (Lm[a]!)[c]! * (Lm[a]!)[c]! * Dm[c]!
    Dm := Dm.set! a s
    Lm := Lm.set! a ((Lm[a]!).set! a 1)
  return (Lm, Dm)

def psdOKF (n : Nat) (N : Nat → Nat → Rat) : Bool :=
  let LD := ldlF n N
  ((List.range n).all fun c => decide (0 ≤ LD.2[c]!)) &&
    ((List.range n).all fun a => (List.range n).all fun b =>
      decide (N a b = lsum (List.range n) fun c => LD.1[a]![c]! * LD.2[c]! * LD.1[b]![c]!))

def fanLowerF (nv : Nat) (y0 w : Nat → Rat) (F0 : Rat) (g : Array Rat) (H : Array (Array Rat)) (σ : Nat → Rat) : Rat :=
  let r := List.range nv
  F0 + lsum r (fun a => g[a]! * y0 a) + lsum r (fun a => lsum r (fun b => H[a]![b]! * y0 a * y0 b)) / 2
    - lsum r (fun a => (g[a]! + lsum r (fun b => H[a]![b]! * y0 b)).abs * w a)
    - lsum r (fun a => σ a * w a ^ 2) / 2

/-- The fast leaf check, given the per-body box data and the y-box centre and half-widths as functions. -/
def leafOKCore (ns : List Nat) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (W : List (Nat × (Rat × Rat)))
    (z : Rat × Rat) (β σ : Nat → Rat) (bb : Nat → BBF) (y0 wv : Nat → Rat) : Bool :=
  let k := ns.length
  let nv := 4 * k - 2
  let FW := W.map fun (i, q) => mkFWit bb i q
  let prs := cycPairsF FW
  let F0 := (prs.map fun (w, w') => pairC0F w.X0 w'.X0 / 2).sum
  let g := fanGF nv prs β
  let H := fanHF nv prs β
  let Hf : Nat → Nat → Rat := fun a b => if a < nv ∧ b < nv then H[a]![b]! else fanHval prs β a b
  ((List.range (k + 1)).all fun i => (bb i).sOK) &&
  decide (2 ≤ k) && decide (3 ≤ W.length) &&
  (FW.all fun w => decide (w.body ≤ k) && memOKF ns V ν w) &&
  decide (dot2Q z z < 1 / 4) &&
  (prs.all fun (w, w') => decide (0 < fanRowF y0 wv z w w')) &&
  windOKF z prs &&
  ((List.range nv).all fun a => decide (0 ≤ σ a)) &&
  psdOKF nv (fun a b => Hf a b + if a = b then σ a else 0) &&
  decide (τ < fanLowerF nv y0 wv F0 g H σ)

/-- The fast leaf check. `W` as (body, point) pairs; `lo hi β σ` as functions. -/
def leafOKF (ns : List Nat) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (lo hi : Nat → Rat) (W : List (Nat × (Rat × Rat)))
    (z : Rat × Rat) (β σ : Nat → Rat) : Bool :=
  let k := ns.length
  let nv := 4 * k - 2
  let bbArr := (Array.range (k + 1)).map fun i => bodyBoxF lo hi i
  let bb : Nat → BBF := fun i => if i ≤ k then bbArr[i]! else bodyBoxF lo hi i
  let y0Arr := (Array.range nv).map fun v => yCentreF bb v
  let wArr := (Array.range nv).map fun v => yHalfF bb v
  let y0 : Nat → Rat := fun v => if v < nv then y0Arr[v]! else yCentreF bb v
  let wv : Nat → Rat := fun v => if v < nv then wArr[v]! else yHalfF bb v
  leafOKCore ns V ν τ W z β σ bb y0 wv

/-! ## Combination leaves -/

/-- Per-fan data of a combination leaf: the fan checks, the constant `A` and the gradient `G` of the affine
minorant. -/
structure FanC where
  ok : Bool
  A : Rat
  G : Array Rat

def fanCore (ns : List Nat) (V : Nat → Nat → Rat × Rat) (ν : Rat) (W : List (Nat × (Rat × Rat))) (z : Rat × Rat)
    (β σ : Nat → Rat) (bb : Nat → BBF) (y0 wv : Nat → Rat) : FanC :=
  let k := ns.length
  let nv := 4 * k - 2
  let FW := W.map fun (i, q) => mkFWit bb i q
  let prs := cycPairsF FW
  let F0 := (prs.map fun (w, w') => pairC0F w.X0 w'.X0 / 2).sum
  let g := fanGF nv prs β
  let H := fanHF nv prs β
  let Hf : Nat → Nat → Rat := fun a b => if a < nv ∧ b < nv then H[a]![b]! else fanHval prs β a b
  let r := List.range nv
  let ok := decide (3 ≤ W.length) &&
    (FW.all fun w => decide (w.body ≤ k) && memOKF ns V ν w) &&
    decide (dot2Q z z < 1 / 4) &&
    (prs.all fun (w, w') => decide (0 < fanRowF y0 wv z w w')) &&
    windOKF z prs &&
    ((List.range nv).all fun a => decide (0 ≤ σ a)) &&
    psdOKF nv (fun a b => Hf a b + if a = b then σ a else 0)
  let A := F0 + lsum r (fun a => g[a]! * y0 a) + lsum r (fun a => lsum r (fun b => H[a]![b]! * y0 a * y0 b)) / 2
    - lsum r (fun a => σ a * wv a ^ 2) / 2
  let G := (Array.range nv).map fun a => g[a]! + lsum r (fun b => H[a]![b]! * y0 b)
  ⟨ok, A, G⟩

def combOKCore (ns : List Nat) (V : Nat → Nat → Rat × Rat) (ν τ : Rat)
    (fans : List (List (Nat × (Rat × Rat)) × (Rat × Rat) × (Nat → Rat) × (Nat → Rat) × Rat))
    (bb : Nat → BBF) (y0 wv : Nat → Rat) : Bool :=
  let k := ns.length
  let nv := 4 * k - 2
  let cs := fans.map fun F => (F.2.2.2.2, fanCore ns V ν F.1 F.2.1 F.2.2.1 F.2.2.2.1 bb y0 wv)
  let S := (cs.map fun (c : Rat × FanC) => c.1).sum
  ((List.range (k + 1)).all fun i => (bb i).sOK) &&
  decide (2 ≤ k) &&
  (cs.all fun (c : Rat × FanC) => decide (0 ≤ c.1) && c.2.ok) &&
  decide (0 < S) &&
  decide (τ * S < (cs.map fun (c : Rat × FanC) => c.1 * c.2.A).sum -
    lsum (List.range nv) (fun a => ((cs.map fun (c : Rat × FanC) => c.1 * c.2.G[a]!).sum).abs * wv a))

/-- The fast combination check. -/
def combOKF (ns : List Nat) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (lo hi : Nat → Rat)
    (fans : List (List (Nat × (Rat × Rat)) × (Rat × Rat) × (Nat → Rat) × (Nat → Rat) × Rat)) : Bool :=
  let k := ns.length
  let nv := 4 * k - 2
  let bbArr := (Array.range (k + 1)).map fun i => bodyBoxF lo hi i
  let bb : Nat → BBF := fun i => if i ≤ k then bbArr[i]! else bodyBoxF lo hi i
  let y0Arr := (Array.range nv).map fun v => yCentreF bb v
  let wArr := (Array.range nv).map fun v => yHalfF bb v
  let y0 : Nat → Rat := fun v => if v < nv then y0Arr[v]! else yCentreF bb v
  let wv : Nat → Rat := fun v => if v < nv then wArr[v]! else yHalfF bb v
  combOKCore ns V ν τ fans bb y0 wv

end LebesgueCover.Fast
