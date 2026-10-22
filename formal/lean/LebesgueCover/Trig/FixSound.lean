import LebesgueCover.Trig.Fix
import Mathlib

/-!
# Soundness of the fixed-point interval and ball arithmetic of `LebesgueCover/Trig/Fix.lean`

`Encl s a x`: the integer pair `a` encloses the real `x` at scale `2^s` (`a.1 ≤ 2^s x ≤ a.2`).
`BEncl z w`: the ball `z` encloses `w ∈ ℂ` (`|w - (re + i im)/2^PR| ≤ r/2^PR`).
Each lemma below is the sentence in the docstring of the corresponding checker function.
-/

namespace LebTrig.Sound

open LebTrig

/-- `a` encloses `x` at scale `2^s`. -/
def Encl (s : ℕ) (a : ℤ × ℤ) (x : ℝ) : Prop := (a.1 : ℝ) ≤ 2 ^ s * x ∧ 2 ^ s * x ≤ (a.2 : ℝ)

/-- The center `(re + i im)/2^PR` of a ball. -/
noncomputable def bc (z : Ball) : ℂ := ⟨(z.re : ℝ) / 2 ^ PR, (z.im : ℝ) / 2 ^ PR⟩

/-- The ball `z` encloses `w`. -/
def BEncl (z : Ball) (w : ℂ) : Prop := ‖w - bc z‖ ≤ (z.r : ℝ) / 2 ^ PR

lemma two_pow_pos (s : ℕ) : (0 : ℝ) < 2 ^ s := by positivity

/-! ## Rounded divisions -/

lemma fdiv_le (a : ℤ) {b : ℕ} (hb : 0 < b) : (fdiv a b : ℝ) ≤ a / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  have := Int.ediv_mul_le a (b := (b : ℤ)) (by exact_mod_cast hb.ne')
  show (((a / (b : ℤ)) : ℤ) : ℝ) * b ≤ a
  exact_mod_cast this

lemma lt_fdiv_add_one (a : ℤ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b < (fdiv a b : ℝ) + 1 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hb']
  have := Int.lt_ediv_add_one_mul_self a (b := (b : ℤ)) (by exact_mod_cast hb)
  show (a : ℝ) < ((((a / (b : ℤ)) : ℤ) : ℝ) + 1) * b
  exact_mod_cast this

lemma le_cdiv (a : ℤ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have := Int.ediv_mul_le (-a) (b := (b : ℤ)) (by exact_mod_cast hb.ne')
  show (a : ℝ) ≤ ((-((-a) / (b : ℤ)) : ℤ) : ℝ) * b
  have h2 : ((((-a) / (b : ℤ)) : ℤ) : ℝ) * b ≤ -(a : ℝ) := by exact_mod_cast this
  push_cast
  linarith

lemma cdiv_lt_add_one (a : ℤ) {b : ℕ} (hb : 0 < b) : (cdiv a b : ℝ) < (a : ℝ) / b + 1 := by
  have h := lt_fdiv_add_one (-a) hb
  have e : (cdiv a b : ℝ) = -(fdiv (-a) b : ℝ) := by
    show ((-((-a) / (b : ℤ)) : ℤ) : ℝ) = -((((-a) / (b : ℤ)) : ℤ) : ℝ)
    push_cast; ring
  rw [e]
  push_cast at h
  rw [neg_div] at h
  linarith

lemma le_cdivN (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (cdivN a b : ℝ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  unfold cdivN
  have h1 := Nat.div_add_mod (a + (b - 1)) b
  have h2 := Nat.mod_lt (a + (b - 1)) hb
  have h3 : a ≤ (a + (b - 1)) / b * b := by
    have : b * ((a + (b - 1)) / b) = (a + (b - 1)) / b * b := Nat.mul_comm _ _
    omega
  exact_mod_cast h3

/-! ## Intervals -/

lemma Encl.lo {s : ℕ} {a : ℤ × ℤ} {x : ℝ} (h : Encl s a x) : (a.1 : ℝ) ≤ 2 ^ s * x := h.1
lemma Encl.hi {s : ℕ} {a : ℤ × ℤ} {x : ℝ} (h : Encl s a x) : 2 ^ s * x ≤ (a.2 : ℝ) := h.2

lemma iadd_encl {s : ℕ} {a b : ℤ × ℤ} {x y : ℝ} (ha : Encl s a x) (hb : Encl s b y) :
    Encl s (iadd a b) (x + y) := by
  unfold iadd Encl at *
  push_cast
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma isub_encl {s : ℕ} {a b : ℤ × ℤ} {x y : ℝ} (ha : Encl s a x) (hb : Encl s b y) :
    Encl s (isub a b) (x - y) := by
  unfold isub Encl at *
  push_cast
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma ineg_encl {s : ℕ} {a : ℤ × ℤ} {x : ℝ} (ha : Encl s a x) : Encl s (ineg a) (-x) := by
  unfold ineg Encl at *
  push_cast
  constructor <;> linarith [ha.1, ha.2]

/-- A linear function on an interval lies between its end values. -/
lemma mul_between {c X a1 a2 : ℝ} (h1 : a1 ≤ X) (h2 : X ≤ a2) :
    min (c * a1) (c * a2) ≤ c * X ∧ c * X ≤ max (c * a1) (c * a2) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h1 hc),
      (mul_le_mul_of_nonneg_left h2 hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h2 hc),
      (mul_le_mul_of_nonpos_left h1 hc).trans (le_max_left _ _)⟩

lemma mul_mem_box {X Y a1 a2 b1 b2 : ℝ} (hX1 : a1 ≤ X) (hX2 : X ≤ a2) (hY1 : b1 ≤ Y) (hY2 : Y ≤ b2) :
    min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2)) ≤ X * Y ∧
      X * Y ≤ max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2)) := by
  obtain ⟨l1, u1⟩ := mul_between (c := Y) hX1 hX2
  obtain ⟨l2, u2⟩ := mul_between (c := a1) hY1 hY2
  obtain ⟨l3, u3⟩ := mul_between (c := a2) hY1 hY2
  rw [mul_comm Y a1, mul_comm Y a2, mul_comm Y X] at l1 u1
  constructor
  · refine le_trans ?_ l1
    rw [le_min_iff]
    exact ⟨(min_le_left _ _).trans l2, (min_le_right _ _).trans l3⟩
  · refine u1.trans ?_
    rw [max_le_iff]
    exact ⟨u2.trans (le_max_left _ _), u3.trans (le_max_right _ _)⟩

lemma imul_encl {s t : ℕ} {a b : ℤ × ℤ} {x y : ℝ} (ha : Encl s a x) (hb : Encl t b y) :
    Encl (s + t) (imul a b) (x * y) := by
  have h := mul_mem_box ha.1 ha.2 hb.1 hb.2
  unfold imul Encl
  simp only [Int.cast_min, Int.cast_max, Int.cast_mul]
  rw [pow_add]
  constructor
  · calc _ ≤ 2 ^ s * x * (2 ^ t * y) := h.1
      _ = 2 ^ s * 2 ^ t * (x * y) := by ring
  · calc 2 ^ s * 2 ^ t * (x * y) = 2 ^ s * x * (2 ^ t * y) := by ring
      _ ≤ _ := h.2

lemma ishr_encl {s k : ℕ} {a : ℤ × ℤ} {x : ℝ} (ha : Encl (s + k) a x) : Encl s (ishr a k) x := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hk' : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hk
  unfold ishr Encl
  have e : ((2 ^ k : ℕ) : ℝ) = 2 ^ k := by push_cast; ring
  constructor
  · refine (fdiv_le a.1 hk).trans ?_
    rw [div_le_iff₀ hk', e, mul_assoc, mul_comm x, ← mul_assoc, ← pow_add]
    exact ha.1
  · refine le_trans ?_ (le_cdiv a.2 hk)
    rw [le_div_iff₀ hk', e, mul_assoc, mul_comm x, ← mul_assoc, ← pow_add]
    exact ha.2

lemma imulr_encl {a b : ℤ × ℤ} {x y : ℝ} (ha : Encl PR a x) (hb : Encl PR b y) :
    Encl PR (imulr a b) (x * y) :=
  ishr_encl (imul_encl ha hb)

lemma iscale_encl {s : ℕ} {a : ℤ × ℤ} {x : ℝ} (ha : Encl s a x) (num : ℕ) {den : ℕ} (hden : 0 < den) :
    Encl s (iscale a num den) (x * num / den) := by
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have hn : (0 : ℝ) ≤ num := Nat.cast_nonneg num
  unfold iscale Encl
  simp only [Int.ofNat_eq_natCast]
  constructor
  · refine (fdiv_le _ hden).trans ?_
    push_cast
    rw [div_le_iff₀ hd, mul_div_assoc', div_mul_cancel₀ _ hd.ne', ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ha.1 hn
  · refine le_trans ?_ (le_cdiv _ hden)
    push_cast
    rw [le_div_iff₀ hd, mul_div_assoc', div_mul_cancel₀ _ hd.ne', ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ha.2 hn

lemma idivN_encl {s : ℕ} {a : ℤ × ℤ} {x : ℝ} (ha : Encl s a x) {n : ℕ} (hn : 0 < n) :
    Encl s (idivN a n) (x / n) := by
  have hd : (0 : ℝ) < n := by exact_mod_cast hn
  unfold idivN Encl
  constructor
  · refine (fdiv_le _ hn).trans ?_
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right ha.1 hd.le
  · refine le_trans ?_ (le_cdiv _ hn)
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right ha.2 hd.le

lemma iscaleI_encl {s : ℕ} {v : ℤ × ℤ} {y : ℝ} (hv : Encl s v y) (x : ℤ) :
    Encl s (iscaleI x v) (x * y) := by
  unfold iscaleI Encl
  split_ifs with hx
  · have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
    push_cast
    constructor
    · nlinarith [hv.1]
    · nlinarith [hv.2]
  · have hx' : (x : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.1 hx))
    push_cast
    constructor
    · nlinarith [hv.2]
    · nlinarith [hv.1]

/-! ## Balls -/

lemma norm_sub_le_of_parts {w c : ℂ} {rx ry : ℝ} (hx : |w.re - c.re| ≤ rx) (hy : |w.im - c.im| ≤ ry) :
    ‖w - c‖ ≤ rx + ry := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  linarith

lemma abs_sub_le_max {X lo hi c : ℝ} (h1 : lo ≤ X) (h2 : X ≤ hi) : |X - c| ≤ max (hi - c) (c - lo) := by
  rw [abs_le]
  constructor
  · linarith [le_max_right (hi - c) (c - lo)]
  · linarith [le_max_left (hi - c) (c - lo)]

lemma toNat_cast_ge (a : ℤ) : (a : ℝ) ≤ ((a.toNat : ℕ) : ℝ) := by
  have := Int.self_le_toNat a
  have h : ((a.toNat : ℕ) : ℝ) = ((a.toNat : ℤ) : ℝ) := by push_cast; rfl
  rw [h]; exact_mod_cast this

/-- One coordinate of `ballOfRect`. -/
lemma coord_le {X : ℝ} {x : ℤ × ℤ} (hx : Encl PR x X) :
    |X - (fdiv (x.1 + x.2) 2 : ℝ) / 2 ^ PR| ≤
      (((max (x.2 - fdiv (x.1 + x.2) 2) (fdiv (x.1 + x.2) 2 - x.1)).toNat : ℕ) : ℝ) / 2 ^ PR := by
  have hS := two_pow_pos PR
  rw [show X - (fdiv (x.1 + x.2) 2 : ℝ) / 2 ^ PR = (2 ^ PR * X - fdiv (x.1 + x.2) 2) / 2 ^ PR by
    field_simp, abs_div, abs_of_pos hS]
  refine div_le_div_of_nonneg_right ?_ hS.le
  refine (abs_sub_le_max hx.1 hx.2).trans ?_
  have := toNat_cast_ge (max (x.2 - fdiv (x.1 + x.2) 2) (fdiv (x.1 + x.2) 2 - x.1))
  push_cast at this
  exact this

lemma ballOfRect_encl {x y : ℤ × ℤ} {w : ℂ} (hx : Encl PR x w.re) (hy : Encl PR y w.im) :
    BEncl (ballOfRect x y) w := by
  unfold BEncl ballOfRect
  refine (norm_sub_le_of_parts (coord_le hx) (coord_le hy)).trans (le_of_eq ?_)
  push_cast
  ring

lemma ballOfReal_encl {x : ℤ × ℤ} {X : ℝ} (hx : Encl PR x X) : BEncl (ballOfReal x) (X : ℂ) := by
  unfold ballOfReal
  refine ballOfRect_encl (by simpa using hx) ?_
  simp [Encl]

lemma BEncl.re_le {z : Ball} {w : ℂ} (h : BEncl z w) : |w.re - z.re / 2 ^ PR| ≤ z.r / 2 ^ PR :=
  calc |w.re - z.re / 2 ^ PR| = |(w - bc z).re| := rfl
    _ ≤ ‖w - bc z‖ := Complex.abs_re_le_norm _
    _ ≤ _ := h

lemma BEncl.im_le {z : Ball} {w : ℂ} (h : BEncl z w) : |w.im - z.im / 2 ^ PR| ≤ z.r / 2 ^ PR :=
  calc |w.im - z.im / 2 ^ PR| = |(w - bc z).im| := rfl
    _ ≤ ‖w - bc z‖ := Complex.abs_im_le_norm _
    _ ≤ _ := h

lemma encl_of_abs {X a r S : ℝ} (hS : 0 < S) (h : |X - a / S| ≤ r / S) : a - r ≤ S * X ∧ S * X ≤ a + r := by
  rw [abs_le] at h
  have e1 : S * (X - a / S) = S * X - a := by field_simp
  have e2 : S * (r / S) = r := by field_simp
  constructor
  · have := mul_le_mul_of_nonneg_left h.1 hS.le
    rw [e1, mul_neg, e2] at this
    linarith
  · have := mul_le_mul_of_nonneg_left h.2 hS.le
    rw [e1, e2] at this
    linarith

lemma ballRe_encl {z : Ball} {w : ℂ} (h : BEncl z w) : Encl PR (ballRe z) w.re := by
  have h1 := encl_of_abs (two_pow_pos PR) h.re_le
  unfold ballRe Encl
  simp only [Int.ofNat_eq_natCast]
  push_cast
  exact h1

lemma ballIm_encl {z : Ball} {w : ℂ} (h : BEncl z w) : Encl PR (ballIm z) w.im := by
  have h1 := encl_of_abs (two_pow_pos PR) h.im_le
  unfold ballIm Encl
  simp only [Int.ofNat_eq_natCast]
  push_cast
  exact h1

lemma ballAdd_encl {z w : Ball} {u v : ℂ} (hz : BEncl z u) (hw : BEncl w v) : BEncl (ballAdd z w) (u + v) := by
  unfold BEncl at *
  have e : bc (ballAdd z w) = bc z + bc w := by
    apply Complex.ext <;> simp [bc, ballAdd, add_div]
  rw [e, show u + v - (bc z + bc w) = (u - bc z) + (v - bc w) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [ballAdd]
  push_cast
  rw [add_div]
  linarith

lemma ballSub_encl {z w : Ball} {u v : ℂ} (hz : BEncl z u) (hw : BEncl w v) : BEncl (ballSub z w) (u - v) := by
  unfold BEncl at *
  have e : bc (ballSub z w) = bc z - bc w := by
    apply Complex.ext <;> simp [bc, ballSub, sub_div]
  rw [e, show u - v - (bc z - bc w) = (u - bc z) - (v - bc w) by ring]
  refine (norm_sub_le _ _).trans ?_
  simp only [ballSub]
  push_cast
  rw [add_div]
  linarith

lemma ballMulI_encl {z : Ball} {u : ℂ} (hz : BEncl z u) : BEncl (ballMulI z) (Complex.I * u) := by
  unfold BEncl at *
  have e : bc (ballMulI z) = Complex.I * bc z := by
    apply Complex.ext <;> simp [bc, ballMulI, neg_div]
  rw [e, ← mul_sub, norm_mul, Complex.norm_I, one_mul]
  simpa [ballMulI] using hz

lemma ballMulInt_encl {z : Ball} {u : ℂ} (hz : BEncl z u) (n : ℤ) : BEncl (ballMulInt z n) ((n : ℂ) * u) := by
  unfold BEncl at *
  have e : bc (ballMulInt z n) = (n : ℂ) * bc z := by
    apply Complex.ext <;> simp [bc, ballMulInt, mul_div_assoc] <;> ring
  rw [e, ← mul_sub, norm_mul, Complex.norm_intCast]
  simp only [ballMulInt, Nat.cast_mul]
  have : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by push_cast [Nat.cast_natAbs]; rfl
  rw [this]
  calc |(n : ℝ)| * ‖u - bc z‖ ≤ |(n : ℝ)| * (z.r / 2 ^ PR) := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    _ = (z.r * |(n : ℝ)|) / 2 ^ PR := by ring

lemma norm_bc_le (z : Ball) : ‖bc z‖ ≤ (l1 z.re z.im : ℝ) / 2 ^ PR := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  simp only [bc, l1, Nat.cast_add]
  rw [abs_div, abs_div, abs_of_pos (two_pow_pos PR)]
  push_cast [Nat.cast_natAbs]
  ring

lemma ONE_eq : ((ONE : ℕ) : ℝ) = 2 ^ PR := by unfold ONE PR; push_cast; ring

lemma ONE_pos : 0 < ONE := by unfold ONE; positivity

/-- Rounding a scale-`2^(2PR)` integer down to scale `2^PR` moves it by less than `1/2^PR`. -/
lemma abs_fdiv_err (X : ℤ) : |(X : ℝ) / 2 ^ PR / 2 ^ PR - (fdiv X ONE : ℝ) / 2 ^ PR| ≤ 1 / 2 ^ PR := by
  have h1 := fdiv_le X ONE_pos
  have h2 := lt_fdiv_add_one X ONE_pos
  rw [ONE_eq] at h1 h2
  rw [show (X : ℝ) / 2 ^ PR / 2 ^ PR - (fdiv X ONE : ℝ) / 2 ^ PR =
      ((X : ℝ) / 2 ^ PR - fdiv X ONE) / 2 ^ PR by ring, abs_div, abs_of_pos (two_pow_pos PR)]
  apply div_le_div_of_nonneg_right _ (two_pow_pos PR).le
  rw [abs_le]
  constructor <;> linarith

lemma le_cdivN_ONE (N : ℕ) : (N : ℝ) / 2 ^ PR ≤ (cdivN N ONE : ℝ) := by
  have := le_cdivN N ONE_pos
  rwa [ONE_eq] at this

/-- Product of two balls. -/
lemma ballMulQ_encl {z w : Ball} {u v : ℂ} {qw : ℕ} (hz : BEncl z u) (hw : BEncl w v)
    (hq : ‖bc w‖ ≤ (qw : ℝ) / 2 ^ PR) : BEncl (ballMulQ z w qw) (u * v) := by
  have hS := two_pow_pos PR
  unfold BEncl at *
  set S : ℝ := 2 ^ PR with hSdef
  set P : ℂ := bc z * bc w with hPdef
  have hP : ‖u * v - P‖ ≤ (z.r * w.r + z.r * qw + l1 z.re z.im * w.r) / S ^ 2 := by
    have e : u * v - P = (u - bc z) * (v - bc w) + (u - bc z) * bc w + bc z * (v - bc w) := by
      rw [hPdef]; ring
    rw [e]
    have hz0 : 0 ≤ ‖u - bc z‖ := norm_nonneg _
    have hw0 : 0 ≤ ‖v - bc w‖ := norm_nonneg _
    have hbz := norm_bc_le z
    calc ‖(u - bc z) * (v - bc w) + (u - bc z) * bc w + bc z * (v - bc w)‖
        ≤ ‖u - bc z‖ * ‖v - bc w‖ + ‖u - bc z‖ * ‖bc w‖ + ‖bc z‖ * ‖v - bc w‖ := by
          refine (norm_add_le _ _).trans ?_
          refine add_le_add ((norm_add_le _ _).trans ?_) (norm_mul_le _ _)
          exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (z.r / S) * (w.r / S) + (z.r / S) * (qw / S) + (l1 z.re z.im / S) * (w.r / S) := by
          gcongr
      _ = (z.r * w.r + z.r * qw + l1 z.re z.im * w.r) / S ^ 2 := by field_simp
  have hR : ‖P - bc (ballMulQ z w qw)‖ ≤ 2 / S := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (P - bc (ballMulQ z w qw)).re =
        ((z.re * w.re - z.im * w.im : ℤ) : ℝ) / S / S - (fdiv (z.re * w.re - z.im * w.im) ONE : ℝ) / S := by
      simp only [hPdef, Complex.sub_re, Complex.mul_re, bc, ballMulQ, hSdef]
      push_cast; ring
    have e2 : (P - bc (ballMulQ z w qw)).im =
        ((z.re * w.im + z.im * w.re : ℤ) : ℝ) / S / S - (fdiv (z.re * w.im + z.im * w.re) ONE : ℝ) / S := by
      simp only [hPdef, Complex.sub_im, Complex.mul_im, bc, ballMulQ, hSdef]
      push_cast; ring
    rw [e1, e2]
    have := abs_fdiv_err (z.re * w.re - z.im * w.im)
    have := abs_fdiv_err (z.re * w.im + z.im * w.re)
    rw [show (2 : ℝ) / S = 1 / S + 1 / S by ring]
    exact add_le_add (by assumption) (by assumption)
  calc ‖u * v - bc (ballMulQ z w qw)‖ ≤ ‖u * v - P‖ + ‖P - bc (ballMulQ z w qw)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (z.r * w.r + z.r * qw + l1 z.re z.im * w.r) / S ^ 2 + 2 / S := add_le_add hP hR
    _ ≤ (ballMulQ z w qw).r / S := by
        have hc := le_cdivN_ONE (l1 z.re z.im * w.r + qw * z.r + z.r * w.r)
        rw [← hSdef] at hc
        have h1 : (z.r * w.r + z.r * qw + l1 z.re z.im * w.r : ℝ) / S ^ 2 ≤
            (cdivN (l1 z.re z.im * w.r + qw * z.r + z.r * w.r) ONE : ℝ) / S := by
          push_cast at hc
          rw [div_le_div_iff₀ (by positivity) hS, sq]
          have := mul_le_mul_of_nonneg_right hc hS.le
          rw [div_mul_cancel₀ _ hS.ne'] at this
          nlinarith
        have e : ((ballMulQ z w qw).r : ℝ) / S =
            (cdivN (l1 z.re z.im * w.r + qw * z.r + z.r * w.r) ONE : ℝ) / S + 2 / S := by
          simp only [ballMulQ]; push_cast; ring
        rw [e]; linarith

/-- Product of a ball with an interval (a real number). -/
lemma ballMulReal_encl {z : Ball} {u : ℂ} {x : ℤ × ℤ} {y : ℝ} (hz : BEncl z u) (hx : Encl PR x y) :
    BEncl (ballMulReal z x) (u * y) := by
  have hS := two_pow_pos PR
  unfold BEncl at *
  set S : ℝ := 2 ^ PR with hSdef
  set xc : ℤ := fdiv (x.1 + x.2) 2 with hxc
  set xr : ℕ := (max (x.2 - xc) (xc - x.1)).toNat with hxr
  have hy : |y - xc / S| ≤ xr / S := coord_le hx
  set P : ℂ := bc z * ((xc : ℝ) / S : ℝ) with hPdef
  have hP : ‖u * y - P‖ ≤ (z.r * xr + z.r * xc.natAbs + l1 z.re z.im * xr) / S ^ 2 := by
    have e : u * (y : ℂ) - P = (u - bc z) * ((y - xc / S : ℝ) : ℂ) + (u - bc z) * ((xc / S : ℝ) : ℂ)
        + bc z * ((y - xc / S : ℝ) : ℂ) := by
      rw [hPdef]; push_cast; ring
    rw [e]
    have hbz := norm_bc_le z
    have hxa : ‖(((xc : ℝ) / S : ℝ) : ℂ)‖ = (xc.natAbs : ℝ) / S := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hS]
      push_cast [Nat.cast_natAbs]; rfl
    have hyn : ‖((y - xc / S : ℝ) : ℂ)‖ ≤ xr / S := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hy
    calc ‖(u - bc z) * ((y - xc / S : ℝ) : ℂ) + (u - bc z) * ((xc / S : ℝ) : ℂ) + bc z * ((y - xc / S : ℝ) : ℂ)‖
        ≤ ‖u - bc z‖ * ‖((y - xc / S : ℝ) : ℂ)‖ + ‖u - bc z‖ * ‖((xc / S : ℝ) : ℂ)‖
            + ‖bc z‖ * ‖((y - xc / S : ℝ) : ℂ)‖ := by
          refine (norm_add_le _ _).trans ?_
          refine add_le_add ((norm_add_le _ _).trans ?_) (norm_mul_le _ _)
          exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (z.r / S) * (xr / S) + (z.r / S) * (xc.natAbs / S) + (l1 z.re z.im / S) * (xr / S) := by
          rw [hxa]
          gcongr
      _ = (z.r * xr + z.r * xc.natAbs + l1 z.re z.im * xr) / S ^ 2 := by field_simp
  have hR : ‖P - bc (ballMulReal z x)‖ ≤ 2 / S := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (P - bc (ballMulReal z x)).re = ((z.re * xc : ℤ) : ℝ) / S / S - (fdiv (z.re * xc) ONE : ℝ) / S := by
      simp only [hPdef, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, bc, ballMulReal,
        hSdef, hxc]
      push_cast; ring
    have e2 : (P - bc (ballMulReal z x)).im = ((z.im * xc : ℤ) : ℝ) / S / S - (fdiv (z.im * xc) ONE : ℝ) / S := by
      simp only [hPdef, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, bc, ballMulReal,
        hSdef, hxc]
      push_cast; ring
    rw [e1, e2]
    have := abs_fdiv_err (z.re * xc)
    have := abs_fdiv_err (z.im * xc)
    rw [show (2 : ℝ) / S = 1 / S + 1 / S by ring]
    exact add_le_add (by assumption) (by assumption)
  calc ‖u * y - bc (ballMulReal z x)‖ ≤ ‖u * y - P‖ + ‖P - bc (ballMulReal z x)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (z.r * xr + z.r * xc.natAbs + l1 z.re z.im * xr) / S ^ 2 + 2 / S := add_le_add hP hR
    _ ≤ (ballMulReal z x).r / S := by
        have hc := le_cdivN_ONE (l1 z.re z.im * xr + xc.natAbs * z.r + z.r * xr)
        rw [← hSdef] at hc
        have h1 : (z.r * xr + z.r * xc.natAbs + l1 z.re z.im * xr : ℝ) / S ^ 2 ≤
            (cdivN (l1 z.re z.im * xr + xc.natAbs * z.r + z.r * xr) ONE : ℝ) / S := by
          push_cast at hc
          rw [div_le_div_iff₀ (by positivity) hS, sq]
          have := mul_le_mul_of_nonneg_right hc hS.le
          rw [div_mul_cancel₀ _ hS.ne'] at this
          nlinarith
        have e : ((ballMulReal z x).r : ℝ) / S =
            (cdivN (l1 z.re z.im * xr + xc.natAbs * z.r + z.r * xr) ONE : ℝ) / S + 2 / S := by
          simp only [ballMulReal]; rw [← hxc, ← hxr]; push_cast; ring
        rw [e]; linarith

/-- `modBound z` bounds the modulus of the center. -/
lemma norm_bc_le_modBound (z : Ball) : ‖bc z‖ ≤ (modBound z : ℝ) / 2 ^ PR := by
  have hS := two_pow_pos PR
  have hsq : ∀ q : ℕ, z.re.natAbs * z.re.natAbs + z.im.natAbs * z.im.natAbs ≤ q * q →
      ‖bc z‖ ≤ (q : ℝ) / 2 ^ PR := by
    intro q hq
    have hq' : ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) ≤ (q : ℝ) ^ 2 := by
      have : ((z.re.natAbs * z.re.natAbs + z.im.natAbs * z.im.natAbs : ℕ) : ℝ) ≤ ((q * q : ℕ) : ℝ) := by
        exact_mod_cast hq
      push_cast [Nat.cast_natAbs] at this
      nlinarith [sq_abs (z.re : ℝ), sq_abs (z.im : ℝ)]
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, Complex.sq_norm]
    simp only [bc, Complex.normSq_mk]
    rw [div_pow]
    field_simp
    nlinarith
  unfold modBound modBoundRI
  simp only
  split_ifs with h1 h2
  · exact hsq _ h1
  · exact hsq _ h2
  · exact norm_bc_le z

/-- Division of a ball by a positive integer (both centers floored, radius `⌈r/n⌉ + 2`). -/
lemma ballDivNat_encl {z : Ball} {u : ℂ} (hz : BEncl z u) {n : ℕ} (hn : 0 < n) :
    BEncl (ballDivNat z n) (u / n) := by
  have hS := two_pow_pos PR
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold BEncl at *
  set S : ℝ := 2 ^ PR with hSdef
  have hP : ‖u / n - bc z / n‖ ≤ (z.r : ℝ) / n / S := by
    rw [← sub_div, norm_div, Complex.norm_natCast, div_div, mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right hz hn'.le |>.trans (le_of_eq (by ring))
  have hR : ‖bc z / n - bc (ballDivNat z n)‖ ≤ 2 / S := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (bc z / n - bc (ballDivNat z n)).re = ((z.re : ℝ) / n - (fdiv z.re n : ℝ)) / S := by
      simp only [Complex.sub_re, Complex.div_natCast_re, bc, ballDivNat, hSdef]
      field_simp
    have e2 : (bc z / n - bc (ballDivNat z n)).im = ((z.im : ℝ) / n - (fdiv z.im n : ℝ)) / S := by
      simp only [Complex.sub_im, Complex.div_natCast_im, bc, ballDivNat, hSdef]
      field_simp
    rw [e1, e2, abs_div, abs_div, abs_of_pos hS]
    have a1 := fdiv_le z.re hn
    have a2 := lt_fdiv_add_one z.re hn
    have b1 := fdiv_le z.im hn
    have b2 := lt_fdiv_add_one z.im hn
    have h1 : |(z.re : ℝ) / n - (fdiv z.re n : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h2 : |(z.im : ℝ) / n - (fdiv z.im n : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    rw [show (2 : ℝ) / S = 1 / S + 1 / S by ring]
    exact add_le_add (div_le_div_of_nonneg_right h1 hS.le) (div_le_div_of_nonneg_right h2 hS.le)
  calc ‖u / n - bc (ballDivNat z n)‖ ≤ ‖u / n - bc z / n‖ + ‖bc z / n - bc (ballDivNat z n)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (z.r : ℝ) / n / S + 2 / S := add_le_add hP hR
    _ ≤ (ballDivNat z n).r / S := by
        have hc := le_cdivN z.r hn
        have e : ((ballDivNat z n).r : ℝ) / S = (cdivN z.r n : ℝ) / S + 2 / S := by
          simp only [ballDivNat]; push_cast; ring
        rw [e]
        have := div_le_div_of_nonneg_right hc hS.le
        linarith

end LebTrig.Sound
