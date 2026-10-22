import LebesgueCover.Rot
import LebesgueCover.Quad

/-!
# The reference leaf checker (rational arithmetic)

Layout for `k` Reuleaux bodies (body `0` is the disk, body `1` is not rotated):
* box coordinates (`d = 3k − 1`): body 1 → `t` at `0, 1`; body `i ≥ 2` → `s` at `3i − 4`, `t` at `3i − 3, 3i − 2`;
* y-variables (`nv = 4k − 2`): body 1 → `Δt` at `0, 1`; body `i ≥ 2` → `Δt` at `4i − 6, 4i − 5`, `C` at `4i − 4`,
  `S` at `4i − 3`, where `s ∈ [lo, hi]`, `m = (lo + hi)/2`, `C = ⟨u(m), u(s)⟩ − 1`, `S = det(u(m), u(s))`.
Every witness position is `X0 + Σ_a y_a L_a`, so the fan area and the fan determinants are quadratics in `y`.
-/

namespace LebesgueCover.Cert

/-! ## Rational helpers -/

def cuQ (s : ℚ) : ℚ := (1 - s ^ 2) / (1 + s ^ 2)
def suQ (s : ℚ) : ℚ := 2 * s / (1 + s ^ 2)
def det2 (a b : ℚ × ℚ) : ℚ := a.1 * b.2 - a.2 * b.1
def dot2 (a b : ℚ × ℚ) : ℚ := a.1 * b.1 + a.2 * b.2
def rot2 (u q : ℚ × ℚ) : ℚ × ℚ := (u.1 * q.1 - u.2 * q.2, u.2 * q.1 + u.1 * q.2)
def J2 (q : ℚ × ℚ) : ℚ × ℚ := (-q.2, q.1)
def uQ (s : ℚ) : ℚ × ℚ := (cuQ s, suQ s)

/-- A witness: body (`0` = disk) and a point in body coordinates. -/
structure Wit where
  body : ℕ
  pt : ℚ × ℚ
deriving Repr, DecidableEq

/-! ## Layout -/

/-- y-index of `Δt_x` of body `i ≥ 1`. -/
def yTx (i : ℕ) : ℕ := if i = 1 then 0 else 4 * i - 6
def yTy (i : ℕ) : ℕ := if i = 1 then 1 else 4 * i - 5
def yC (i : ℕ) : ℕ := 4 * i - 4
def yS (i : ℕ) : ℕ := 4 * i - 3
/-- box index of `t_x`, `t_y`, `s` of body `i ≥ 1`. -/
def bTx (i : ℕ) : ℕ := if i = 1 then 0 else 3 * i - 3
def bTy (i : ℕ) : ℕ := if i = 1 then 1 else 3 * i - 2
def bS (i : ℕ) : ℕ := 3 * i - 4

/-- Data of a leaf box, per body. -/
structure BodyBox where
  tc : ℚ × ℚ       -- centre of `t`
  ht : ℚ × ℚ       -- half-widths of `t`
  M : ℚ × ℚ        -- centre rotation `u(m)` (`(1, 0)` for bodies 0, 1)
  Cmax : ℚ         -- `C ∈ [−Cmax, 0]`
  Smax : ℚ         -- `|S| ≤ Smax`
  sOK : Bool       -- `0 ≤ lo ≤ hi ≤ 1` for the `s`-range
deriving Repr

def bodyBox (lo hi : ℕ → ℚ) (i : ℕ) : BodyBox :=
  if i = 0 then ⟨(0, 0), (0, 0), (1, 0), 0, 0, true⟩
  else
    let tc := ((lo (bTx i) + hi (bTx i)) / 2, (lo (bTy i) + hi (bTy i)) / 2)
    let ht := ((hi (bTx i) - lo (bTx i)) / 2, (hi (bTy i) - lo (bTy i)) / 2)
    if i = 1 then ⟨tc, ht, (1, 0), 0, 0, true⟩
    else
      let sl := lo (bS i); let sh := hi (bS i); let m := (sl + sh) / 2
      let M := uQ m
      let Cmax := max (1 - dot2 M (uQ sl)) (1 - dot2 M (uQ sh))
      let Smax := max |det2 M (uQ sl)| |det2 M (uQ sh)|
      ⟨tc, ht, M, Cmax, Smax, decide (0 ≤ sl ∧ sl ≤ sh ∧ sh ≤ 1)⟩

/-- Linearization of a witness: `x = X0 + Σ_a y_a L a`. -/
def witX0 (bb : ℕ → BodyBox) (w : Wit) : ℚ × ℚ :=
  if w.body = 0 then w.pt
  else
    let B := bb w.body
    let a := rot2 B.M w.pt
    (a.1 + B.tc.1, a.2 + B.tc.2)

def witL (bb : ℕ → BodyBox) (w : Wit) (v : ℕ) : ℚ × ℚ :=
  if w.body = 0 then (0, 0)
  else
    let a := rot2 (bb w.body).M w.pt
    if v = yTx w.body then (1, 0)
    else if v = yTy w.body then (0, 1)
    else if 2 ≤ w.body ∧ v = yC w.body then a
    else if 2 ≤ w.body ∧ v = yS w.body then J2 a
    else (0, 0)

/-! ## Quadratic pieces of a pair `det(P0 + L y, Q0 + M y)` -/

/-- constant, linear and quadratic coefficients. -/
def pairC0 (P0 Q0 : ℚ × ℚ) : ℚ := det2 P0 Q0
def pairG (P0 Q0 : ℚ × ℚ) (L M : ℕ → ℚ × ℚ) (a : ℕ) : ℚ := det2 P0 (M a) + det2 (L a) Q0
def pairA (L M : ℕ → ℚ × ℚ) (a b : ℕ) : ℚ := det2 (L a) (M b)

open Finset in
/-- Lower bound of `c0 + Σ g_a y_a + Σ_{a,b} A_ab y_a y_b` over `|y − y0| ≤ w` (absolute values). -/
def quadLowerAbs (nv : ℕ) (c0 : ℚ) (g : ℕ → ℚ) (A : ℕ → ℕ → ℚ) (y0 w : ℕ → ℚ) : ℚ :=
  c0 + ∑ a ∈ range nv, g a * y0 a + ∑ a ∈ range nv, ∑ b ∈ range nv, A a b * y0 a * y0 b
    - ∑ a ∈ range nv, |g a + ∑ b ∈ range nv, (A a b + A b a) * y0 b| * w a
    - ∑ a ∈ range nv, ∑ b ∈ range nv, |A a b| * w a * w b

/-! ## The y-box -/

/-- Body owning a y-variable, and the kind of the variable (0: Δt_x, 1: Δt_y, 2: C, 3: S). -/
def yBody (v : ℕ) : ℕ := if v < 2 then 1 else (v + 6) / 4
def yKind (v : ℕ) : ℕ := if v < 2 then v else (v + 6) % 4

def yCentre (bb : ℕ → BodyBox) (v : ℕ) : ℚ :=
  if yKind v = 2 then -(bb (yBody v)).Cmax / 2 else 0

def yHalf (bb : ℕ → BodyBox) (v : ℕ) : ℚ :=
  let B := bb (yBody v)
  match yKind v with
  | 0 => B.ht.1
  | 1 => B.ht.2
  | 2 => B.Cmax / 2
  | _ => B.Smax

/-! ## The checks -/

/-- Rational approximations of the vertices `V_{n,l}` of the Reuleaux polygons, and their error radius `ν`. -/
structure VertTable where
  V : ℕ → ℕ → ℚ × ℚ   -- `V n l`
  ν : ℚ

/-- Witness membership: disk `|q|² ≤ 1/4`; Reuleaux `n`: `|q − Ṽ_{n,l}|² ≤ (1 − ν)²` for all `l < n`. -/
def memOK (ns : List ℕ) (vt : VertTable) (w : Wit) : Bool :=
  if w.body = 0 then decide (dot2 w.pt w.pt ≤ 1 / 4)
  else
    let n := ns.getD (w.body - 1) 0
    decide (0 < n) && (List.range n).all fun l =>
      let d := (w.pt.1 - (vt.V n l).1, w.pt.2 - (vt.V n l).2)
      decide (dot2 d d ≤ (1 - vt.ν) ^ 2)

/-- Fan row `j`: lower bound of `det(x_j − z, x_{j+1} − z)` on the box. -/
def fanRow (nv : ℕ) (bb : ℕ → BodyBox) (z : ℚ × ℚ) (w w' : Wit) : ℚ :=
  let P0 := witX0 bb w; let Q0 := witX0 bb w'
  let P := (P0.1 - z.1, P0.2 - z.2); let Q := (Q0.1 - z.1, Q0.2 - z.2)
  quadLowerAbs nv (pairC0 P Q) (pairG P Q (witL bb w) (witL bb w')) (pairA (witL bb w) (witL bb w'))
    (yCentre bb) (yHalf bb)

/-- Cyclic consecutive pairs of a list. -/
def cycPairs {α : Type} : List α → List (α × α)
  | [] => []
  | a :: t => List.zip (a :: t) (t ++ [a])

/-- Upper bound for the angle `θ ∈ (0, π)` from `a` to `b` (when `det(a, b) > 0`):
`min(det/dot, π⁺/2)` if `dot > 0` (`θ ≤ tan θ` and `θ < π/2`), and `min(π⁺, π⁺/2 − dot/det)` if `dot ≤ 0`
(`θ = π/2 + arctan(−dot/det)`), with `π⁺ = 3.1416 > π`. -/
def angleUB (P Q : ℚ × ℚ) : ℚ :=
  if 0 < dot2 P Q then min (det2 P Q / dot2 P Q) (31416 / 20000)
  else min (31416 / 10000) (31416 / 20000 - dot2 P Q / det2 P Q)

/-- Winding certificate at the centre placement (`y = 0`): every `det > 0` and `Σ angleUB < 4π⁻`,
`π⁻ = 3.1415 < π`. -/
def windOK (bb : ℕ → BodyBox) (z : ℚ × ℚ) (W : List Wit) : Bool :=
  let prs := (cycPairs W).map fun (w, w') =>
    let P0 := witX0 bb w; let Q0 := witX0 bb w'
    ((P0.1 - z.1, P0.2 - z.2), (Q0.1 - z.1, Q0.2 - z.2))
  (prs.all fun (P, Q) => decide (0 < det2 P Q)) &&
    decide ((prs.map fun (P, Q) => angleUB P Q).sum < 4 * (31415 / 10000))

open Finset in
/-- The fan area as a quadratic in `y`: `F = F0 + Σ g_a y_a + (1/2) Σ H_ab y_a y_b` (plus the identity terms). -/
structure FanQuad where
  F0 : ℚ
  g : ℕ → ℚ
  H : ℕ → ℕ → ℚ

open Finset in
def fanQuad (bb : ℕ → BodyBox) (W : List Wit) (β : ℕ → ℚ) : FanQuad :=
  let prs := cycPairs W
  let F0 := (prs.map fun (w, w') => pairC0 (witX0 bb w) (witX0 bb w') / 2).sum
  let g : ℕ → ℚ := fun a =>
    (prs.map fun (w, w') => pairG (witX0 bb w) (witX0 bb w') (witL bb w) (witL bb w') a / 2).sum +
      (if yKind a = 2 then 2 * β (yBody a) else 0)
  let H : ℕ → ℕ → ℚ := fun a b =>
    (prs.map fun (w, w') => (pairA (witL bb w) (witL bb w') a b + pairA (witL bb w) (witL bb w') b a) / 2).sum +
      (if a = b ∧ (yKind a = 2 ∨ yKind a = 3) then 2 * β (yBody a) else 0)
  ⟨F0, g, H⟩

open Finset in
/-- The `LDLᵀ` recursion for an `n × n` matrix `N` (given as a function), returning `(L, D)` as functions. -/
def ldl (n : ℕ) (N : ℕ → ℕ → ℚ) : (ℕ → ℕ → ℚ) × (ℕ → ℚ) :=
  -- column by column, with memo arrays
  Id.run do
    let mut Lm : Array (Array ℚ) := Array.replicate n (Array.replicate n 0)
    let mut Dm : Array ℚ := Array.replicate n 0
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
    return (fun a b => (Lm[a]!)[b]!, fun a => Dm[a]!)

open Finset in
/-- PSD certificate for `N`: the computed `L, D` satisfy `N = L D Lᵀ` exactly and `D ≥ 0`. -/
def psdOK (n : ℕ) (N : ℕ → ℕ → ℚ) : Bool :=
  let LD := ldl n N
  ((List.range n).all fun c => decide (0 ≤ LD.2 c)) &&
    ((List.range n).all fun a => (List.range n).all fun b =>
      decide (N a b = ∑ c ∈ range n, LD.1 a c * LD.2 c * LD.1 b c))

open Finset in
/-- The bound on `F` over the box. -/
def fanLower (nv : ℕ) (bb : ℕ → BodyBox) (Q : FanQuad) (σ : ℕ → ℚ) : ℚ :=
  let y0 := yCentre bb; let w := yHalf bb
  Q.F0 + ∑ a ∈ range nv, Q.g a * y0 a + (∑ a ∈ range nv, ∑ b ∈ range nv, Q.H a b * y0 a * y0 b) / 2
    - ∑ a ∈ range nv, |Q.g a + ∑ b ∈ range nv, Q.H a b * y0 b| * w a
    - (∑ a ∈ range nv, σ a * w a ^ 2) / 2

/-- The leaf check. `ns` lists the Reuleaux bodies (`k = ns.length`), `lo hi` the box (indexed by `ℕ`). -/
def leafOK (ns : List ℕ) (vt : VertTable) (τ : ℚ) (lo hi : ℕ → ℚ) (W : List Wit) (z : ℚ × ℚ)
    (β σ : ℕ → ℚ) : Bool :=
  let k := ns.length
  let nv := 4 * k - 2
  let bb := bodyBox lo hi
  let Q := fanQuad bb W β
  ((List.range (k + 1)).all fun i => (bb i).sOK) &&
  decide (2 ≤ k) && decide (3 ≤ W.length) &&
  (W.all fun w => decide (w.body ≤ k) && memOK ns vt w) &&
  decide (dot2 z z < 1 / 4) &&
  ((cycPairs W).all fun (w, w') => decide (0 < fanRow nv bb z w w')) &&
  windOK bb z W &&
  ((List.range nv).all fun a => decide (0 ≤ σ a)) &&
  psdOK nv (fun a b => Q.H a b + if a = b then σ a else 0) &&
  decide (τ < fanLower nv bb Q σ)

/-! ## Combination leaves (several fans on one box; Lemma 3.8 of the paper) -/

/-- The checks of one fan of a combination leaf (everything of `leafOK` except the box checks and the bound). -/
def fanOK (ns : List ℕ) (vt : VertTable) (lo hi : ℕ → ℚ) (W : List Wit) (z : ℚ × ℚ) (β σ : ℕ → ℚ) : Bool :=
  let k := ns.length
  let nv := 4 * k - 2
  let bb := bodyBox lo hi
  let Q := fanQuad bb W β
  decide (3 ≤ W.length) &&
  (W.all fun w => decide (w.body ≤ k) && memOK ns vt w) &&
  decide (dot2 z z < 1 / 4) &&
  ((cycPairs W).all fun (w, w') => decide (0 < fanRow nv bb z w w')) &&
  windOK bb z W &&
  ((List.range nv).all fun a => decide (0 ≤ σ a)) &&
  psdOK nv (fun a b => Q.H a b + if a = b then σ a else 0)

open Finset in
/-- Constant of the affine minorant of a fan on the box: `F(y₀) − (1/2) Σ σ_a w_a²`. -/
def fanA (nv : ℕ) (bb : ℕ → BodyBox) (Q : FanQuad) (σ : ℕ → ℚ) : ℚ :=
  let y0 := yCentre bb; let w := yHalf bb
  Q.F0 + ∑ a ∈ range nv, Q.g a * y0 a + (∑ a ∈ range nv, ∑ b ∈ range nv, Q.H a b * y0 a * y0 b) / 2
    - (∑ a ∈ range nv, σ a * w a ^ 2) / 2

open Finset in
/-- Gradient of a fan's quadratic at the box centre. -/
def fanG (nv : ℕ) (bb : ℕ → BodyBox) (Q : FanQuad) (a : ℕ) : ℚ :=
  Q.g a + ∑ b ∈ range nv, Q.H a b * yCentre bb b

open Finset in
/-- A combination leaf: fans `(W_i, z_i, β_i, σ_i)` with weights `λ_i ≥ 0`, `S = Σ λ_i > 0`, and
`τ S < Σ λ_i A_i − Σ_a |Σ_i λ_i G_{i,a}| w_a`. -/
def combOK (ns : List ℕ) (vt : VertTable) (τ : ℚ) (lo hi : ℕ → ℚ)
    (fans : List (List Wit × (ℚ × ℚ) × (ℕ → ℚ) × (ℕ → ℚ) × ℚ)) : Bool :=
  let k := ns.length
  let nv := 4 * k - 2
  let bb := bodyBox lo hi
  let S := (fans.map fun F => F.2.2.2.2).sum
  ((List.range (k + 1)).all fun i => (bb i).sOK) &&
  decide (2 ≤ k) &&
  (fans.all fun F => decide (0 ≤ F.2.2.2.2) && fanOK ns vt lo hi F.1 F.2.1 F.2.2.1 F.2.2.2.1) &&
  decide (0 < S) &&
  decide (τ * S < (fans.map fun F => F.2.2.2.2 * fanA nv bb (fanQuad bb F.1 F.2.2.1) F.2.2.2.1).sum
    - ∑ a ∈ range nv, |(fans.map fun F => F.2.2.2.2 * fanG nv bb (fanQuad bb F.1 F.2.2.1) a).sum| * yHalf bb a)

end LebesgueCover.Cert
