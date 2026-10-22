/-!
# Fixed-point helpers (core Lean only)

A real number `x` is enclosed by `(lo, hi) : Int × Int` at precision `p` when `lo ≤ 2^p x ≤ hi`; the checker uses
`p = PR = 128` throughout. Complex numbers are enclosed by balls (`Ball`): center `(re + i im) / 2^PR`, radius
`r / 2^PR`. Every function below states, in its docstring, the enclosure it produces from enclosures of its inputs
(SPEC_W2, section 0); these sentences are the proof obligations of the soundness proof.
-/

namespace LebTrig

/-- Scale of all enclosures. -/
def PR : Nat := 128

/-- `2^PR`. -/
def ONE : Nat := 2 ^ 128

/-- `⌊a / b⌋` for `b > 0`. -/
def fdiv (a : Int) (b : Nat) : Int := Int.ediv a (Int.ofNat b)

/-- `⌈a / b⌉` for `b > 0`. -/
def cdiv (a : Int) (b : Nat) : Int := Int.neg (Int.ediv (Int.neg a) (Int.ofNat b))

/-- `⌈a / b⌉` for natural numbers, `b > 0`. -/
def cdivN (a b : Nat) : Nat := (a + (b - 1)) / b

/-! ## Interval arithmetic on `Int × Int` (exact) -/

/-- If `a` encloses `x` and `b` encloses `y` (same scale `s`), then `iadd a b` encloses `x + y` (scale `s`). -/
def iadd (a b : Int × Int) : Int × Int := (a.1 + b.1, a.2 + b.2)

/-- If `a` encloses `x` and `b` encloses `y`, then `isub a b` encloses `x - y`. -/
def isub (a b : Int × Int) : Int × Int := (a.1 - b.2, a.2 - b.1)

/-- If `a` encloses `x`, then `ineg a` encloses `-x`. -/
def ineg (a : Int × Int) : Int × Int := (-a.2, -a.1)

/-- If `a` encloses `x` at scale `s` and `b` encloses `y` at scale `t`, then `imul a b` encloses `x y` at scale
`s + t`. -/
def imul (a b : Int × Int) : Int × Int :=
  let p1 := a.1 * b.1
  let p2 := a.1 * b.2
  let p3 := a.2 * b.1
  let p4 := a.2 * b.2
  (min (min p1 p2) (min p3 p4), max (max p1 p2) (max p3 p4))

/-- If `a` encloses `x` at scale `s + k`, then `ishr a k` encloses `x` at scale `s` (outward rounding). -/
def ishr (a : Int × Int) (k : Nat) : Int × Int := (fdiv a.1 (2 ^ k), cdiv a.2 (2 ^ k))

/-- If `a` encloses `x` and `b` encloses `y` (both at `2^PR`), then `imulr a b` encloses `x y` at `2^PR`. -/
def imulr (a b : Int × Int) : Int × Int := ishr (imul a b) PR

/-- If `a` encloses `x` (scale `s`) and `num ≥ 0`, `den > 0`, then `iscale a num den` encloses `x num / den`
(scale `s`). -/
def iscale (a : Int × Int) (num den : Nat) : Int × Int :=
  (fdiv (a.1 * Int.ofNat num) den, cdiv (a.2 * Int.ofNat num) den)

/-- If `a` encloses `x` (scale `s`), then `idivN a n` encloses `x / n` (scale `s`), `n > 0`. -/
def idivN (a : Int × Int) (n : Nat) : Int × Int := (fdiv a.1 n, cdiv a.2 n)

/-- If `v` encloses `y`, then `iscaleI x v` encloses `x y` for an integer `x` (scale unchanged). -/
def iscaleI (x : Int) (v : Int × Int) : Int × Int :=
  if 0 ≤ x then (x * v.1, x * v.2) else (x * v.2, x * v.1)

/-! ## Complex balls -/

/-- A ball `⟨re, im, r⟩` encloses every `z ∈ ℂ` with `|z - (re + i im)/2^PR| ≤ r/2^PR`. -/
structure Ball where
  re : Int
  im : Int
  r : Nat
deriving Repr, DecidableEq, Inhabited

/-- If `x` encloses `Re z` and `y` encloses `Im z` (at `2^PR`), then `ballOfRect x y` encloses `z`. -/
def ballOfRect (x y : Int × Int) : Ball :=
  let cr := fdiv (x.1 + x.2) 2
  let ci := fdiv (y.1 + y.2) 2
  ⟨cr, ci, (max (x.2 - cr) (cr - x.1)).toNat + (max (y.2 - ci) (ci - y.1)).toNat⟩

/-- The real number enclosed by `x` (at `2^PR`), as a ball. -/
def ballOfReal (x : Int × Int) : Ball := ballOfRect x (0, 0)

/-- If `z` encloses `w`, then `ballRe z` encloses `Re w` (at `2^PR`). -/
def ballRe (z : Ball) : Int × Int := (z.re - Int.ofNat z.r, z.re + Int.ofNat z.r)

/-- If `z` encloses `w`, then `ballIm z` encloses `Im w` (at `2^PR`). -/
def ballIm (z : Ball) : Int × Int := (z.im - Int.ofNat z.r, z.im + Int.ofNat z.r)

/-- If `z` encloses `u` and `w` encloses `v`, then `ballAdd z w` encloses `u + v`. -/
def ballAdd (z w : Ball) : Ball := ⟨z.re + w.re, z.im + w.im, z.r + w.r⟩

/-- If `z` encloses `u` and `w` encloses `v`, then `ballSub z w` encloses `u - v`. -/
def ballSub (z w : Ball) : Ball := ⟨z.re - w.re, z.im - w.im, z.r + w.r⟩

/-- If `z` encloses `u`, then `ballMulI z` encloses `i u`. -/
def ballMulI (z : Ball) : Ball := ⟨-z.im, z.re, z.r⟩

/-- If `z` encloses `u`, then `ballMulInt z n` encloses `n u` (integer `n`). -/
def ballMulInt (z : Ball) (n : Int) : Ball := ⟨z.re * n, z.im * n, z.r * n.natAbs⟩

/-- If `z` encloses `u`, then `ballDivNat z n` encloses `u / n` (`n > 0`; both centers rounded down, so the center
moves by less than `√2 < 2` units: radius `⌈r/n⌉ + 2`). -/
def ballDivNat (z : Ball) (n : Nat) : Ball := ⟨fdiv z.re n, fdiv z.im n, cdivN z.r n + 2⟩

/-- `|re| + |im|`, an upper bound of the modulus of `re + i im`. -/
def l1 (re im : Int) : Nat := re.natAbs + im.natAbs

/-- If `z` encloses `u`, `w` encloses `v` and `qw ≥ |w.re + i w.im|` (all at `2^PR`), then `ballMulQ z w qw`
encloses `u v`: center `⌊z_c w_c⌋` (each part), radius `⌈(|z_c|₁ r_w + qw r_z + r_z r_w)/2^PR⌉ + 2`. -/
def ballMulQ (z w : Ball) (qw : Nat) : Ball :=
  ⟨fdiv (z.re * w.re - z.im * w.im) ONE, fdiv (z.re * w.im + z.im * w.re) ONE,
   cdivN (l1 z.re z.im * w.r + qw * z.r + z.r * w.r) ONE + 2⟩

/-- If `z` encloses `u` and `x` encloses the real number `y` (at `2^PR`), then `ballMulReal z x` encloses `u y`. -/
def ballMulReal (z : Ball) (x : Int × Int) : Ball :=
  let xc := fdiv (x.1 + x.2) 2
  let xr := (max (x.2 - xc) (xc - x.1)).toNat
  ⟨fdiv (z.re * xc) ONE, fdiv (z.im * xc) ONE,
   cdivN (l1 z.re z.im * xr + xc.natAbs * z.r + z.r * xr) ONE + 2⟩

/-- Newton iteration for `⌈√s⌉` with fuel (only a hint: `modBound` checks its result). -/
def isqrtIter (s : Nat) : Nat → Nat → Nat
  | 0, g => g
  | fuel + 1, g =>
    let nx := (g + s / g) / 2
    if nx < g then isqrtIter s fuel nx else g

/-- A natural number `q` with `q^2 ≥ re^2 + im^2`, i.e. `q ≥ |re + i im|`: the Newton value (rounded up) if it passes
the test, otherwise `|re| + |im|`. -/
def modBoundRI (re im : Int) : Nat :=
  let s := re.natAbs * re.natAbs + im.natAbs * im.natAbs
  let g := isqrtIter s 400 (2 ^ (Nat.log2 s / 2 + 1))
  if s ≤ g * g then g else if s ≤ (g + 1) * (g + 1) then g + 1 else l1 re im

/-- `modBound z ≥ |center of z|` (scale `2^PR`). -/
def modBound (z : Ball) : Nat := modBoundRI z.re z.im

end LebTrig
