import LebesgueCover.Trig.Fix

/-!
# π, cos and sin at rational multiples of π (core Lean only)

`π ∈ [PLO, PHI] / 2^PIS` from `3.14159265358979323846 < π < 3.14159265358979323847` (Mathlib `Real.pi_gt_d20`,
`Real.pi_lt_d20`). For an angle `x ∈ [0, π/4]` the exact rational Taylor sums of cos (powers `x^0 .. x^32`) and sin
(`x^1 .. x^33`) are evaluated at the rational end points `x = a PLO/(b 2^PIS)` and `a PHI/(b 2^PIS)`; cos is decreasing
and sin increasing on `[0, π/4]`, and the Taylor remainder (`Complex.exp_bound` with `n = 34`) is `< 2^-135` for
`|x| ≤ 0.8`, which the final `± 1` (at `2^PR`) covers. Other angles are reduced by exact index arithmetic.
-/

namespace LebTrig

/-- Scale of the π enclosure. -/
def PIS : Nat := 68
/-- `PLO / 2^PIS ≤ 3.14159265358979323846 < π`. -/
def PLO : Nat := 314159265358979323846 * 2 ^ 68 / 10 ^ 20
/-- `π < 3.14159265358979323847 ≤ PHI / 2^PIS`. -/
def PHI : Nat := (314159265358979323847 * 2 ^ 68 + (10 ^ 20 - 1)) / 10 ^ 20

/-- Encloses `2^PR π`. -/
def piEncl : Int × Int := (Int.ofNat (PLO * 2 ^ (PR - PIS)), Int.ofNat (PHI * 2 ^ (PR - PIS)))

/-- Number of Taylor terms. -/
def NT : Nat := 17

/-- Horner step for the cosine sum: for `x² = y/z`, `(num, den) ↦ (q - y num, q)` with `q = z (2m+1)(2m+2) den`. -/
def cosLoop (y z : Nat) : Nat → Int × Nat → Int × Nat
  | 0, acc => acc
  | m + 1, acc =>
    let q : Nat := z * ((2 * m + 1) * (2 * m + 2)) * acc.2
    cosLoop y z m (Int.ofNat q - Int.ofNat y * acc.1, q)

/-- Exact `∑_{m < NT} (-1)^m x^(2m)/(2m)!` for `x = a/b` (`b > 0`), as `(num, den)` with `den > 0`. -/
def cosSeries (a b : Nat) : Int × Nat := cosLoop (a * a) (b * b) (NT - 1) (1, 1)

/-- Horner step for the sine sum: `q = z (2m+2)(2m+3) den`. -/
def sinLoop (y z : Nat) : Nat → Int × Nat → Int × Nat
  | 0, acc => acc
  | m + 1, acc =>
    let q : Nat := z * ((2 * m + 2) * (2 * m + 3)) * acc.2
    sinLoop y z m (Int.ofNat q - Int.ofNat y * acc.1, q)

/-- Exact `∑_{m < NT} (-1)^m x^(2m+1)/(2m+1)!` for `x = a/b` (`b > 0`), as `(num, den)` with `den > 0`. -/
def sinSeries (a b : Nat) : Int × Nat :=
  let r := sinLoop (a * a) (b * b) (NT - 1) (1, 1)
  (r.1 * Int.ofNat a, r.2 * b)

/-- `(⌊2^PR n/d⌋ - 1, ⌈2^PR n/d⌉ + 1)`: encloses `2^PR y` for every real `y` with `|y - n/d| < 2^-PR`. -/
def rnd (nd : Int × Nat) : Int × Int :=
  (fdiv (nd.1 * Int.ofNat ONE) nd.2 - 1, cdiv (nd.1 * Int.ofNat ONE) nd.2 + 1)

/-- Encloses `2^PR cos(a π/b)` for `0 ≤ 4a ≤ b`, `b > 0` (angle in `[0, π/4]`, cos decreasing). -/
def cosQ (a b : Nat) : Int × Int :=
  let d := b * 2 ^ PIS
  ((rnd (cosSeries (a * PHI) d)).1, (rnd (cosSeries (a * PLO) d)).2)

/-- Encloses `2^PR sin(a π/b)` for `0 ≤ 4a ≤ b`, `b > 0` (angle in `[0, π/4]`, sin increasing). -/
def sinQ (a b : Nat) : Int × Int :=
  let d := b * 2 ^ PIS
  ((rnd (sinSeries (a * PLO) d)).1, (rnd (sinSeries (a * PHI) d)).2)

/-- Reduction of `cos(a π/b)`, `0 ≤ a ≤ b`, to `[0, π/4]`: `cos x`, `sin(π/2 - x)`, `-sin(x - π/2)`, `-cos(π - x)`. -/
def cosRed (a b : Nat) : Int × Int :=
  if 4 * a ≤ b then cosQ a b
  else if 4 * a ≤ 2 * b then sinQ (b - 2 * a) (2 * b)
  else if 4 * a ≤ 3 * b then ineg (sinQ (2 * a - b) (2 * b))
  else ineg (cosQ (b - a) b)

/-- Encloses `2^PR cos(a π/b)` for an integer `a` and `b > 0` (evenness and `2π`-periodicity). -/
def cosPi (a : Int) (b : Nat) : Int × Int :=
  let a1 := a.natAbs % (2 * b)
  let a2 := if b < a1 then 2 * b - a1 else a1
  cosRed a2 b

/-- Encloses `2^PR sin(a π/b)` for an integer `a` and `b > 0` (`sin x = cos(x - π/2)`). -/
def sinPi (a : Int) (b : Nat) : Int × Int := cosPi (2 * a - Int.ofNat b) (2 * b)

end LebTrig
