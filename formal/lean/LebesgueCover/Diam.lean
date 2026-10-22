import LebesgueCover.Reduce
import LebesgueCover.Basic

/-!
# The bodies have diameter `1`; from `Hull5Statement` to `Λ ≥ 0.8366`

For odd `n = 2m + 1 ≥ 3` the Reuleaux polygon `B_n = ⋂_l D(V_l, 1)` has diameter `1`. With `δ = π/(2n)` and
`θ_l = 2πl/n`, the differences `V_l − V_{l+m}` and `V_l − V_{l+m+1}` are the unit vectors `e^{i(θ_l ∓ δ)}`, so for a
direction `u = e^{i(θ_l + α)}` with `|α| ≤ δ` every point `x ∈ B_n` has `⟨x − V_l, u⟩ ≤ 0` (`V_l` is the support point
in direction `u`). Every direction is within `δ` of `±e^{iθ_l}` for some `l`, so for `p, q ∈ B_n` with
`p − q = r u` (`r ≥ 0`): `r = ⟨p − V_l, u⟩ + ⟨V_l − q, u⟩ ≤ 0 + |V_l − q| ≤ 1`. The vertices `V_0, V_m` are at
distance `1`. The disk has diameter `1` as well, and both are convex, so a weak universal cover contains congruent
copies of all five bodies and hence of the convex hull of their union.
-/

open MeasureTheory Set Complex

namespace LebesgueCover.Cert

/-- `dotC z w = Re(z w̄)`, the Euclidean inner product of `ℂ = ℝ²`. -/
def dotC (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

lemma dotC_sub_left (a b w : ℂ) : dotC (a - b) w = dotC a w - dotC b w := by
  simp only [dotC, sub_re, sub_im]; ring

lemma dotC_add_left (a b w : ℂ) : dotC (a + b) w = dotC a w + dotC b w := by
  simp only [dotC, add_re, add_im]; ring

lemma dotC_real_mul (r : ℝ) (u w : ℂ) : dotC ((r : ℂ) * u) w = r * dotC u w := by
  simp only [dotC, mul_re, mul_im, ofReal_re, ofReal_im]; ring

lemma dotC_self (u : ℂ) : dotC u u = ‖u‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; rfl

lemma dotC_le_norm (a u : ℂ) (hu : ‖u‖ = 1) : dotC a u ≤ ‖a‖ := by
  have e : dotC a u = (a * (starRingEnd ℂ) u).re := by
    simp only [dotC, mul_re, conj_re, conj_im]; ring
  rw [e]
  calc (a * (starRingEnd ℂ) u).re ≤ ‖a * (starRingEnd ℂ) u‖ := Complex.re_le_norm _
    _ = ‖a‖ := by rw [norm_mul, Complex.norm_conj, hu, mul_one]

/-- `⟨z, w e^{iβ}⟩ = cos β ⟨z, w⟩ + sin β ⟨z, i w⟩`. -/
lemma dotC_rot (z w : ℂ) (β : ℝ) :
    dotC z (w * exp ((β : ℂ) * I)) = Real.cos β * dotC z w + Real.sin β * dotC z (I * w) := by
  simp only [dotC, mul_re, mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, I_re, I_im]; ring

/-- If `‖z + g‖ ≤ 1` for a unit `g` then `⟨z, g⟩ ≤ 0`. -/
lemma dotC_nonpos_of_norm_add {z g : ℂ} (hg : ‖g‖ = 1) (h : ‖z + g‖ ≤ 1) : dotC z g ≤ 0 := by
  have h1 : ‖z + g‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z + g)]
  have h2 : ‖g‖ ^ 2 = 1 := by rw [hg]; norm_num
  rw [Complex.sq_norm, Complex.normSq_apply] at h1 h2
  simp only [add_re, add_im] at h1
  simp only [dotC]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

lemma cos_half_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.cos (Real.pi / (2 * n)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply Real.cos_pos_of_mem_Ioo; constructor
  · linarith [show 0 < Real.pi / (2 * n) by positivity, Real.pi_pos]
  · rw [div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) (by norm_num)]; linarith

lemma circR_two_cos {n : ℕ} (hn : 2 ≤ n) : circR n * (2 * Real.cos (Real.pi / (2 * n))) = 1 := by
  have hc := cos_half_pos hn
  unfold circR; field_simp

/-- `R_n (e^{iδ} + e^{-iδ}) = 1`. -/
lemma circR_exp_sum {n : ℕ} (hn : 2 ≤ n) :
    (circR n : ℂ) * (exp (((Real.pi / (2 * n) : ℝ) : ℂ) * I) + exp (-(((Real.pi / (2 * n) : ℝ) : ℂ) * I))) = 1 := by
  have h := circR_two_cos hn
  rw [← neg_mul, ← Complex.two_cos, ← Complex.ofReal_cos]
  exact_mod_cast h

/-- `V_l − V_{(l+m) % n} = e^{i(θ_l − δ)}` for `n = 2m + 1`. -/
lemma vert_sub_m {n m : ℕ} (hnm : n = 2 * m + 1) (hm : 1 ≤ m) (l : ℕ) :
    vertC n l - vertC n ((l + m) % n) = exp (((2 * Real.pi * l / n - Real.pi / (2 * n) : ℝ) : ℂ) * I) := by
  have hn0 : 0 < n := by omega
  have hnr : (n : ℝ) = 2 * m + 1 := by exact_mod_cast hnm
  have hRB := circR_exp_sum (n := n) (by omega)
  rw [← rot_vertC hn0 l m, vertC_eq]
  set δ := Real.pi / (2 * n) with hδ
  set θ := 2 * Real.pi * l / n with hθ
  have e1 : (2 * Real.pi * m / n : ℝ) = Real.pi - 2 * δ := by
    rw [hδ]; field_simp; rw [hnr]; ring
  rw [e1]
  set A := exp ((θ : ℂ) * I)
  set B := exp ((δ : ℂ) * I)
  set C := exp (-((δ : ℂ) * I))
  set R := (circR n : ℂ)
  have hBC : B * C = 1 := by rw [← Complex.exp_add]; simp
  have hE : exp (((Real.pi - 2 * δ : ℝ) : ℂ) * I) = -(C * C) := by
    rw [show ((Real.pi - 2 * δ : ℝ) : ℂ) * I = (Real.pi : ℂ) * I + (-((δ : ℂ) * I)) + (-((δ : ℂ) * I)) by
      push_cast; ring, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hT : exp (((θ - δ : ℝ) : ℂ) * I) = A * C := by
    rw [show ((θ - δ : ℝ) : ℂ) * I = (θ : ℂ) * I + (-((δ : ℂ) * I)) by push_cast; ring, Complex.exp_add]
  rw [hE, hT]
  linear_combination (A * C) * hRB - (R * A) * hBC

/-- `V_l − V_{(l+m+1) % n} = e^{i(θ_l + δ)}` for `n = 2m + 1`. -/
lemma vert_sub_m1 {n m : ℕ} (hnm : n = 2 * m + 1) (hm : 1 ≤ m) (l : ℕ) :
    vertC n l - vertC n ((l + (m + 1)) % n) = exp (((2 * Real.pi * l / n + Real.pi / (2 * n) : ℝ) : ℂ) * I) := by
  have hn0 : 0 < n := by omega
  have hnr : (n : ℝ) = 2 * m + 1 := by exact_mod_cast hnm
  have hRB := circR_exp_sum (n := n) (by omega)
  rw [← rot_vertC hn0 l (m + 1), vertC_eq]
  set δ := Real.pi / (2 * n) with hδ
  set θ := 2 * Real.pi * l / n with hθ
  have e1 : (2 * Real.pi * ((m + 1 : ℕ) : ℝ) / n : ℝ) = Real.pi + 2 * δ := by
    rw [hδ]; push_cast; field_simp; rw [hnr]; ring
  rw [e1]
  set A := exp ((θ : ℂ) * I)
  set B := exp ((δ : ℂ) * I)
  set C := exp (-((δ : ℂ) * I))
  set R := (circR n : ℂ)
  have hBC : B * C = 1 := by rw [← Complex.exp_add]; simp
  have hE : exp (((Real.pi + 2 * δ : ℝ) : ℂ) * I) = -(B * B) := by
    rw [show ((Real.pi + 2 * δ : ℝ) : ℂ) * I = (Real.pi : ℂ) * I + (δ : ℂ) * I + (δ : ℂ) * I by
      push_cast; ring, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hT : exp (((θ + δ : ℝ) : ℂ) * I) = A * B := by
    rw [show ((θ + δ : ℝ) : ℂ) * I = (θ : ℂ) * I + (δ : ℂ) * I by push_cast; ring, Complex.exp_add]
  rw [hE, hT]
  linear_combination (A * B) * hRB - (R * A) * hBC

lemma mem_ball_of_reuleauxC {n : ℕ} {x : ℂ} (hx : x ∈ reuleauxC n) {j : ℕ} (hj : j < n) :
    ‖x - vertC n j‖ ≤ 1 := by
  simp only [reuleauxC, Set.mem_iInter, Metric.mem_closedBall, Finset.mem_range] at hx
  rw [← dist_eq_norm]; exact hx j hj

/-- **Support at a vertex.** For `x ∈ B_n` (`n = 2m + 1 ≥ 3`) and `|α| ≤ π/(2n)`: `⟨x − V_l, e^{i(θ_l + α)}⟩ ≤ 0`. -/
lemma vert_support {n m : ℕ} (hnm : n = 2 * m + 1) (hm : 1 ≤ m) (l : ℕ) {x : ℂ} (hx : x ∈ reuleauxC n)
    {α : ℝ} (hα : |α| ≤ Real.pi / (2 * n)) :
    dotC (x - vertC n l) (exp (((2 * Real.pi * l / n + α : ℝ) : ℂ) * I)) ≤ 0 := by
  have hn0 : 0 < n := by omega
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  set δ := Real.pi / (2 * n) with hδ
  set θ := 2 * Real.pi * l / n with hθ
  set z := x - vertC n l
  set w := exp ((θ : ℂ) * I)
  have hsplit : ∀ β : ℝ, exp (((θ + β : ℝ) : ℂ) * I) = w * exp ((β : ℂ) * I) := by
    intro β; rw [show ((θ + β : ℝ) : ℂ) * I = (θ : ℂ) * I + (β : ℂ) * I by push_cast; ring, Complex.exp_add]
  -- the two discs through `V_l`
  have h1 := mem_ball_of_reuleauxC hx (Nat.mod_lt (l + m) hn0)
  have h2 := mem_ball_of_reuleauxC hx (Nat.mod_lt (l + (m + 1)) hn0)
  have g1 := vert_sub_m hnm hm l
  have g2 := vert_sub_m1 hnm hm l
  rw [← hθ, ← hδ] at g1 g2
  have e1 : x - vertC n ((l + m) % n) = z + exp (((θ - δ : ℝ) : ℂ) * I) := by rw [← g1]; ring
  have e2 : x - vertC n ((l + (m + 1)) % n) = z + exp (((θ + δ : ℝ) : ℂ) * I) := by rw [← g2]; ring
  rw [e1] at h1; rw [e2] at h2
  have d1 := dotC_nonpos_of_norm_add (norm_exp_I _) h1
  have d2 := dotC_nonpos_of_norm_add (norm_exp_I _) h2
  rw [sub_eq_add_neg, hsplit, dotC_rot, Real.cos_neg, Real.sin_neg] at d1
  rw [hsplit, dotC_rot] at d2
  rw [hsplit, dotC_rot]
  set X := dotC z w
  set Y := dotC z (I * w)
  -- trigonometric bounds for `|α| ≤ δ ≤ π/2`
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ Real.pi / 2 := by
    rw [hδ, div_le_div_iff_of_pos_left Real.pi_pos (by positivity) (by norm_num)]; linarith
  have hcδ : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by
    have : δ < Real.pi / 2 := by
      rw [hδ, div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) (by norm_num)]; linarith
    exact this⟩
  have hab := abs_le.mp hα
  have hcα : Real.cos δ ≤ Real.cos α := by
    rw [← Real.cos_abs α]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg α) (by linarith [Real.pi_pos]) hα
  have hsα1 : Real.sin α ≤ Real.sin δ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hδle hab.2
  have hsα2 : -Real.sin δ ≤ Real.sin α := by
    rw [← Real.sin_neg]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hab.1
  have hX : X ≤ 0 := by nlinarith
  have hXc : Real.cos α * X ≤ Real.cos δ * X := by nlinarith
  rcases le_total 0 Y with hY | hY
  · nlinarith [mul_le_mul_of_nonneg_left hsα1 hY]
  · nlinarith [mul_le_mul_of_nonpos_left hsα2 hY]

/-- Every direction is within `π/(2n)` of `±e^{iθ_l}` (`n = 2m + 1`). -/
lemma dir_cover {n m : ℕ} (hnm : n = 2 * m + 1) (ψ : ℝ) :
    ∃ l < n, ∃ α : ℝ, |α| ≤ Real.pi / (2 * n) ∧
      (exp ((ψ : ℂ) * I) = exp (((2 * Real.pi * l / n + α : ℝ) : ℂ) * I) ∨
       exp ((ψ : ℂ) * I) = -exp (((2 * Real.pi * l / n + α : ℝ) : ℂ) * I)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnr : (n : ℝ) = 2 * m + 1 := by exact_mod_cast hnm
  have hpi := Real.pi_pos
  set r : ℤ := round (ψ * n / Real.pi) with hr
  have hrr := abs_sub_round (ψ * n / Real.pi)
  rw [← hr] at hrr
  set α := ψ - Real.pi * r / n with hαdef
  have hα : |α| ≤ Real.pi / (2 * n) := by
    have e : α = Real.pi / n * (ψ * n / Real.pi - r) := by rw [hαdef]; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    calc Real.pi / n * |ψ * n / Real.pi - r| ≤ Real.pi / n * (1 / 2) := mul_le_mul_of_nonneg_left hrr (by positivity)
      _ = Real.pi / (2 * n) := by field_simp
  -- reduce an integer index mod `n`
  have hred : ∀ l0 : ℤ, ∃ l < n, ∃ q : ℤ, (l0 : ℝ) = l + n * q := by
    intro l0
    have hl_nonneg : 0 ≤ l0 % n := Int.emod_nonneg _ (by exact_mod_cast (by omega : n ≠ 0))
    have hl_lt : l0 % n < n := Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : 0 < n))
    refine ⟨(l0 % n).toNat, by omega, l0 / n, ?_⟩
    have hsplit : l0 = l0 % n + n * (l0 / n) := by have := Int.emod_add_ediv_mul l0 (n : ℤ); linarith
    have hlr : (((l0 % n).toNat : ℕ) : ℝ) = ((l0 % n : ℤ) : ℝ) := by
      have := Int.toNat_of_nonneg hl_nonneg; exact_mod_cast this
    rw [hlr]; exact_mod_cast hsplit
  have hper : ∀ (x : ℝ) (q : ℤ), exp (((x + 2 * Real.pi * q : ℝ) : ℂ) * I) = exp ((x : ℂ) * I) := by
    intro x q
    rw [show ((x + 2 * Real.pi * q : ℝ) : ℂ) * I = (x : ℂ) * I + q * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rcases Int.even_or_odd' r with ⟨j, hj | hj⟩
  · obtain ⟨l, hl, q, hq⟩ := hred j
    refine ⟨l, hl, α, hα, Or.inl ?_⟩
    have e : ψ = (2 * Real.pi * l / n + α) + 2 * Real.pi * q := by
      have hjr : (r : ℝ) = 2 * j := by exact_mod_cast hj
      rw [hαdef, hjr, hq]; field_simp; ring
    rw [e, hper]
  · obtain ⟨l, hl, q, hq⟩ := hred (j - m)
    refine ⟨l, hl, α, hα, Or.inr ?_⟩
    have e : ψ = ((2 * Real.pi * l / n + α) + 2 * Real.pi * q) + Real.pi := by
      have hjr : (r : ℝ) = 2 * j + 1 := by exact_mod_cast hj
      have hq' : (j : ℝ) = l + n * q + m := by push_cast at hq; linarith
      rw [hαdef, hjr, hq']; field_simp; rw [hnr]; ring
    rw [e, show (((2 * Real.pi * l / n + α + 2 * Real.pi * q + Real.pi : ℝ)) : ℂ) * I =
      (((2 * Real.pi * l / n + α + 2 * Real.pi * q : ℝ)) : ℂ) * I + (Real.pi : ℂ) * I by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I, hper]
    ring

/-- **Two points of `B_n` are at distance at most `1`** (odd `n ≥ 3`). -/
theorem reuleauxC_dist_le {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) {p q : ℂ} (hp : p ∈ reuleauxC n)
    (hq : q ∈ reuleauxC n) : ‖p - q‖ ≤ 1 := by
  obtain ⟨m, hnm⟩ := hn
  have hm : 1 ≤ m := by omega
  have key : ∀ {x y : ℂ}, x ∈ reuleauxC n → y ∈ reuleauxC n → ∀ l < n, ∀ α : ℝ, |α| ≤ Real.pi / (2 * n) →
      ∀ r : ℝ, x - y = (r : ℂ) * exp (((2 * Real.pi * l / n + α : ℝ) : ℂ) * I) → r ≤ 1 := by
    intro x y hx hy l hl α hα r hxy
    set u := exp (((2 * Real.pi * l / n + α : ℝ) : ℂ) * I)
    have hu : ‖u‖ = 1 := norm_exp_I _
    have s1 := vert_support hnm hm l hx hα
    have s2 : dotC (vertC n l - y) u ≤ 1 := by
      have := dotC_le_norm (vertC n l - y) u hu
      have hb := mem_ball_of_reuleauxC hy hl
      rw [norm_sub_rev] at hb; linarith
    have e : dotC (x - y) u = dotC (x - vertC n l) u + dotC (vertC n l - y) u := by
      rw [← dotC_add_left]; ring_nf
    have e2 : dotC (x - y) u = r := by rw [hxy, dotC_real_mul, dotC_self, hu]; ring
    linarith
  obtain ⟨l, hl, α, hα, h | h⟩ := dir_cover hnm (arg (p - q))
  · exact key hp hq l hl α hα ‖p - q‖ (by rw [← h, norm_mul_exp_arg_mul_I])
  · apply key hq hp l hl α hα ‖p - q‖
    have := norm_mul_exp_arg_mul_I (p - q)
    rw [h] at this
    linear_combination this

/-- **`B_n` has diameter `1`** in `ℂ` (odd `n ≥ 3`). -/
theorem ediam_reuleauxC {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) : Metric.ediam (reuleauxC n) = 1 := by
  apply le_antisymm
  · have := Metric.ediam_le_of_forall_dist_le (s := reuleauxC n) (C := 1)
      (fun x hx y hy => by rw [dist_eq_norm]; exact reuleauxC_dist_le hn h3 hx hy)
    simpa using this
  · obtain ⟨m, hnm⟩ := hn
    have h0 := vert_mem ⟨m, hnm⟩ h3 (l := 0) (by omega)
    have hk := vert_mem ⟨m, hnm⟩ h3 (l := m) (by omega)
    have hd : edist (vertC n 0) (vertC n m) = 1 := by
      have := vert_sub_m hnm (by omega) 0
      rw [zero_add, Nat.mod_eq_of_lt (by omega)] at this
      rw [edist_dist, dist_eq_norm, this, norm_exp_I, ENNReal.ofReal_one]
    rw [← hd]; exact Metric.edist_le_ediam_of_mem h0 hk

/-- `B_n` has diameter `1` (odd `n ≥ 3`). -/
theorem ediam_reuleaux {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) : Metric.ediam (reuleaux n) = 1 := by
  rw [← LinearIsometryEquiv.ediam_image eC, eC_reuleaux]; exact ediam_reuleauxC hn h3

/-- The disk has diameter `1`. -/
theorem ediam_disk : Metric.ediam disk = 1 := by
  rw [← LinearIsometryEquiv.ediam_image eC, eC_disk]
  apply le_antisymm
  · have := Metric.ediam_le_of_forall_dist_le (s := diskC) (C := 1) (fun x hx y hy => by
      simp only [diskC, Metric.mem_closedBall, dist_zero_right] at hx hy
      rw [dist_eq_norm]
      calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 1 := by linarith)
    simpa using this
  · have h1 : (1 / 2 : ℂ) ∈ diskC := by
      simp only [diskC, Metric.mem_closedBall, dist_zero_right]; norm_num
    have h2 : (-(1 / 2) : ℂ) ∈ diskC := by
      simp only [diskC, Metric.mem_closedBall, dist_zero_right, norm_neg]; norm_num
    have hd : edist (1 / 2 : ℂ) (-(1 / 2)) = 1 := by
      rw [edist_dist, dist_eq_norm, sub_neg_eq_add, add_halves, norm_one, ENNReal.ofReal_one]
    rw [← hd]; exact Metric.edist_le_ediam_of_mem h1 h2

theorem convex_reuleaux (n : ℕ) : Convex ℝ (reuleaux n) :=
  convex_iInter₂ fun _ _ => convex_closedBall _ _

theorem convex_disk : Convex ℝ disk := convex_closedBall _ _

/-- **`Hull5Statement → WeakMain5Statement`**: a weak universal cover contains congruent copies of `D, B₃, B₅, B₇, B₉`
(convex, diameter `1`), hence the convex hull of their union. -/
theorem weak5_of_hull5 (h : Hull5Statement) : WeakMain5Statement := by
  intro Ω hΩ
  obtain ⟨hconv, hcov⟩ := hΩ
  obtain ⟨φ0, h0⟩ := hcov disk convex_disk ediam_disk
  obtain ⟨φ1, h1⟩ := hcov (reuleaux 3) (convex_reuleaux 3) (ediam_reuleaux ⟨1, rfl⟩ le_rfl)
  obtain ⟨φ2, h2⟩ := hcov (reuleaux 5) (convex_reuleaux 5) (ediam_reuleaux ⟨2, rfl⟩ (by norm_num))
  obtain ⟨φ3, h3⟩ := hcov (reuleaux 7) (convex_reuleaux 7) (ediam_reuleaux ⟨3, rfl⟩ (by norm_num))
  obtain ⟨φ4, h4⟩ := hcov (reuleaux 9) (convex_reuleaux 9) (ediam_reuleaux ⟨4, rfl⟩ (by norm_num))
  refine le_trans h ?_
  let g : Fin 5 → (Plane ≃ᵢ Plane) := ![φ0, φ1, φ2, φ3, φ4]
  calc hull5 ≤ volume (convexHull ℝ (g 0 '' disk ∪ g 1 '' reuleaux 3 ∪ g 2 '' reuleaux 5 ∪ g 3 '' reuleaux 7 ∪
        g 4 '' reuleaux 9)) := iInf_le (fun g : Fin 5 → (Plane ≃ᵢ Plane) => volume (convexHull ℝ (g 0 '' disk ∪
          g 1 '' reuleaux 3 ∪ g 2 '' reuleaux 5 ∪ g 3 '' reuleaux 7 ∪ g 4 '' reuleaux 9))) g
    _ ≤ volume Ω := by
      apply measure_mono
      apply convexHull_min _ hconv
      simp only [g, union_subset_iff]
      exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩

/-- **`Hull5Statement → Main5Statement`** (`Λ ≥ 0.8366`). -/
theorem main5_of_hull5 (h : Hull5Statement) : Main5Statement := main5_of_weak5 (weak5_of_hull5 h)

/-- The same bridge for the four-body bound: `Hull4Statement → WeakMainStatement`. -/
theorem weak_of_hull4 (h : Hull4Statement) : WeakMainStatement := by
  intro Ω hΩ
  obtain ⟨hconv, hcov⟩ := hΩ
  obtain ⟨φ0, h0⟩ := hcov disk convex_disk ediam_disk
  obtain ⟨φ1, h1⟩ := hcov (reuleaux 3) (convex_reuleaux 3) (ediam_reuleaux ⟨1, rfl⟩ le_rfl)
  obtain ⟨φ2, h2⟩ := hcov (reuleaux 5) (convex_reuleaux 5) (ediam_reuleaux ⟨2, rfl⟩ (by norm_num))
  obtain ⟨φ3, h3⟩ := hcov (reuleaux 7) (convex_reuleaux 7) (ediam_reuleaux ⟨3, rfl⟩ (by norm_num))
  refine le_trans h ?_
  let g : Fin 4 → (Plane ≃ᵢ Plane) := ![φ0, φ1, φ2, φ3]
  calc hull4 ≤ volume (convexHull ℝ (g 0 '' disk ∪ g 1 '' reuleaux 3 ∪ g 2 '' reuleaux 5 ∪ g 3 '' reuleaux 7)) :=
        iInf_le (fun g : Fin 4 → (Plane ≃ᵢ Plane) => volume (convexHull ℝ (g 0 '' disk ∪ g 1 '' reuleaux 3 ∪
          g 2 '' reuleaux 5 ∪ g 3 '' reuleaux 7))) g
    _ ≤ volume Ω := by
      apply measure_mono
      apply convexHull_min _ hconv
      simp only [g, union_subset_iff]
      exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩

/-- `Hull4Statement → MainStatement` (`Λ ≥ 0.836`). -/
theorem main_of_hull4 (h : Hull4Statement) : MainStatement := main_of_weak (weak_of_hull4 h)

/-- `Λ ≥ 0.8366` gives `Λ ≥ 0.836` (weak reading). -/
theorem weak_of_weak5 (h : WeakMain5Statement) : WeakMainStatement := fun Ω hΩ =>
  le_trans (ENNReal.ofReal_le_ofReal (by norm_num)) (h Ω hΩ)

/-- `Λ ≥ 0.8366` gives `Λ ≥ 0.836`. -/
theorem main_of_main5 (h : Main5Statement) : MainStatement :=
  le_trans (ENNReal.ofReal_le_ofReal (by norm_num)) h

end LebesgueCover.Cert
