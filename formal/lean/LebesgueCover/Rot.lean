import Mathlib

/-!
# Rotations by rational points of the circle

`u(s) = ((1 − s²), 2s)/(1 + s²)` (`s = tan(ρ/2)`). For a leaf `s ∈ [lo, hi]` with centre `m`, the rotation `u(s)` is
`u(m)` followed by the rotation `(cos δ, sin δ) = (⟨u(m), u(s)⟩, det(u(m), u(s)))`, and
`1 − cos δ = 2(s − m)²/((1 + s²)(1 + m²))`, `sin δ = 2(s − m)(1 + sm)/((1 + s²)(1 + m²))`; both are monotone in `s` on
each side of `m` (for `0 ≤ lo ≤ m ≤ hi ≤ 1`), so their ranges are attained at `lo` and `hi`.
-/

namespace LebesgueCover

/-- `cos ρ` for `s = tan(ρ/2)`. -/
noncomputable def cu (s : ℝ) : ℝ := (1 - s ^ 2) / (1 + s ^ 2)
/-- `sin ρ` for `s = tan(ρ/2)`. -/
noncomputable def su (s : ℝ) : ℝ := 2 * s / (1 + s ^ 2)

lemma one_add_sq_pos (s : ℝ) : 0 < 1 + s ^ 2 := by positivity

lemma cu_sq_add_su_sq (s : ℝ) : cu s ^ 2 + su s ^ 2 = 1 := by
  unfold cu su
  have := one_add_sq_pos s
  field_simp
  ring

/-- `⟨u(m), u(s)⟩ = 1 − 2(s − m)²/((1 + s²)(1 + m²))`. -/
lemma dot_u (m s : ℝ) :
    cu m * cu s + su m * su s = 1 - 2 * (s - m) ^ 2 / ((1 + s ^ 2) * (1 + m ^ 2)) := by
  unfold cu su
  have h1 := one_add_sq_pos s
  have h2 := one_add_sq_pos m
  field_simp
  ring

/-- `det(u(m), u(s)) = 2(s − m)(1 + sm)/((1 + s²)(1 + m²))`. -/
lemma det_u (m s : ℝ) :
    cu m * su s - su m * cu s = 2 * (s - m) * (1 + s * m) / ((1 + s ^ 2) * (1 + m ^ 2)) := by
  unfold cu su
  have h1 := one_add_sq_pos s
  have h2 := one_add_sq_pos m
  field_simp
  ring

/-- `u(s) = u(m) · (cos δ, sin δ)` as a product of complex numbers. -/
lemma u_compose (m s : ℝ) :
    cu s = cu m * (cu m * cu s + su m * su s) - su m * (cu m * su s - su m * cu s) ∧
    su s = su m * (cu m * cu s + su m * su s) + cu m * (cu m * su s - su m * cu s) := by
  have h := cu_sq_add_su_sq m
  exact ⟨by linear_combination (-(cu s)) * h, by linear_combination (-(su s)) * h⟩

lemma dot_sq_add_det_sq (m s : ℝ) :
    (cu m * cu s + su m * su s) ^ 2 + (cu m * su s - su m * cu s) ^ 2 = 1 := by
  have h1 := cu_sq_add_su_sq m
  have h2 := cu_sq_add_su_sq s
  linear_combination (cu s ^ 2 + su s ^ 2) * h1 + h2

/-- Monotonicity of `1 − cos δ` on the right of the centre. -/
lemma one_sub_dot_le_right {m s hi : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hms : m ≤ s) (hshi : s ≤ hi) :
    1 - (cu m * cu s + su m * su s) ≤ 1 - (cu m * cu hi + su m * su hi) := by
  rw [dot_u, dot_u]
  have h1 := one_add_sq_pos s
  have h2 := one_add_sq_pos m
  have h3 := one_add_sq_pos hi
  simp only [sub_sub_cancel]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- (s − m)² (1 + hi²) ≤ (hi − m)² (1 + s²): the difference is (hi − s)((1 + 2 hi m − m²) s + hi − 2m − m² hi)
  have key : (hi - m) ^ 2 * (1 + s ^ 2) - (s - m) ^ 2 * (1 + hi ^ 2) =
      (hi - s) * ((1 + 2 * hi * m - m ^ 2) * s + hi - 2 * m - m ^ 2 * hi) := by ring
  have hlin : 0 ≤ (1 + 2 * hi * m - m ^ 2) * s + hi - 2 * m - m ^ 2 * hi := by
    have e : (1 + 2 * hi * m - m ^ 2) * s + hi - 2 * m - m ^ 2 * hi =
        (1 + 2 * hi * m - m ^ 2) * (s - m) + (hi - m) * (1 + m ^ 2) := by ring
    rw [e]
    have : 0 ≤ 1 + 2 * hi * m - m ^ 2 := by nlinarith
    have := mul_nonneg this (sub_nonneg.mpr hms)
    have := mul_nonneg (sub_nonneg.mpr (hms.trans hshi)) (le_of_lt (one_add_sq_pos m))
    linarith
  have := mul_nonneg (sub_nonneg.mpr hshi) hlin
  nlinarith [key]

/-- Monotonicity of `1 − cos δ` on the left of the centre. -/
lemma one_sub_dot_le_left {m s lo : ℝ} (hlo0 : 0 ≤ lo) (hm1 : m ≤ 1) (hlos : lo ≤ s) (hsm : s ≤ m) :
    1 - (cu m * cu s + su m * su s) ≤ 1 - (cu m * cu lo + su m * su lo) := by
  rw [dot_u, dot_u]
  have h1 := one_add_sq_pos s
  have h2 := one_add_sq_pos m
  have h3 := one_add_sq_pos lo
  simp only [sub_sub_cancel]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (lo - m) ^ 2 * (1 + s ^ 2) - (s - m) ^ 2 * (1 + lo ^ 2) =
      (s - lo) * ((1 + 2 * lo * m - m ^ 2) * (m - s) + (m - lo) * (1 + m ^ 2)) := by ring
  have hm0 : 0 ≤ m := (hlo0.trans hlos).trans hsm
  have hc : 0 ≤ 1 + 2 * lo * m - m ^ 2 := by nlinarith
  have hlin : 0 ≤ (1 + 2 * lo * m - m ^ 2) * (m - s) + (m - lo) * (1 + m ^ 2) := by
    have := mul_nonneg hc (sub_nonneg.mpr hsm)
    have := mul_nonneg (sub_nonneg.mpr (hlos.trans hsm)) (le_of_lt h2)
    linarith
  have := mul_nonneg (sub_nonneg.mpr hlos) hlin
  nlinarith [key]

/-- Monotonicity of `|sin δ|` on the right of the centre. -/
lemma det_le_right {m s hi : ℝ} (hm0 : 0 ≤ m) (hhi1 : hi ≤ 1) (hms : m ≤ s) (hshi : s ≤ hi) :
    |cu m * su s - su m * cu s| ≤ |cu m * su hi - su m * cu hi| := by
  rw [det_u, det_u]
  have h1 := one_add_sq_pos s
  have h2 := one_add_sq_pos m
  have h3 := one_add_sq_pos hi
  have hs0 : 0 ≤ s := hm0.trans hms
  have hhi0 : 0 ≤ hi := hs0.trans hshi
  rw [abs_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.mpr hms)) (by positivity))
      (by positivity)),
    abs_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.mpr (hms.trans hshi)))
      (by positivity)) (by positivity))]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (hi - m) * (1 + hi * m) * (1 + s ^ 2) - (s - m) * (1 + s * m) * (1 + hi ^ 2) =
      (hi - s) * ((2 * m + hi * m ^ 2 - hi) * s + 1 + 2 * hi * m - m ^ 2) := by ring
  have hq : 0 ≤ (2 * m + hi * m ^ 2 - hi) * s + 1 + 2 * hi * m - m ^ 2 := by
    -- linear in s, nonnegative at s = m and at s = hi
    have em : (2 * m + hi * m ^ 2 - hi) * m + 1 + 2 * hi * m - m ^ 2 = (1 + m ^ 2) * (1 + hi * m) := by ring
    have eh : (2 * m + hi * m ^ 2 - hi) * hi + 1 + 2 * hi * m - m ^ 2 = (1 - hi ^ 2) * (1 - m ^ 2) + 4 * hi * m := by
      ring
    have hm1 : m ≤ 1 := (hms.trans hshi).trans hhi1
    have A : 0 ≤ (1 + m ^ 2) * (1 + hi * m) := by positivity
    have B : 0 ≤ (1 - hi ^ 2) * (1 - m ^ 2) + 4 * hi * m := by
      have : 0 ≤ 1 - hi ^ 2 := by nlinarith
      have : 0 ≤ 1 - m ^ 2 := by nlinarith
      positivity
    -- convex combination
    rcases eq_or_lt_of_le (hms.trans hshi) with heq | hlt
    · have : s = m := le_antisymm (heq ▸ hshi) hms
      rw [this, em]; exact A
    · have hne : hi - m ≠ 0 := by linarith
      have hθ : s = m + (s - m) / (hi - m) * (hi - m) := by rw [div_mul_cancel₀ _ hne]; ring
      have ht0 : 0 ≤ (s - m) / (hi - m) := div_nonneg (sub_nonneg.mpr hms) (by linarith)
      have ht1 : (s - m) / (hi - m) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      set θ := (s - m) / (hi - m)
      have : (2 * m + hi * m ^ 2 - hi) * s + 1 + 2 * hi * m - m ^ 2 =
          (1 - θ) * ((2 * m + hi * m ^ 2 - hi) * m + 1 + 2 * hi * m - m ^ 2) +
            θ * ((2 * m + hi * m ^ 2 - hi) * hi + 1 + 2 * hi * m - m ^ 2) := by
        rw [hθ]; ring
      rw [this, em, eh]
      have := mul_nonneg (sub_nonneg.mpr ht1) A
      have := mul_nonneg ht0 B
      linarith
  have := mul_nonneg (sub_nonneg.mpr hshi) hq
  nlinarith [key]

/-- Monotonicity of `|sin δ|` on the left of the centre. -/
lemma det_le_left {m s lo : ℝ} (hlo0 : 0 ≤ lo) (hm1 : m ≤ 1) (hlos : lo ≤ s) (hsm : s ≤ m) :
    |cu m * su s - su m * cu s| ≤ |cu m * su lo - su m * cu lo| := by
  rw [det_u, det_u]
  have h1 := one_add_sq_pos s
  have h2 := one_add_sq_pos m
  have h3 := one_add_sq_pos lo
  have hs0 : 0 ≤ s := hlo0.trans hlos
  have hm0 : 0 ≤ m := hs0.trans hsm
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) (by positivity)),
    abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) (by positivity))]
  rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (lo - m) * (1 + lo * m) * (1 + s ^ 2) - (s - m) * (1 + s * m) * (1 + lo ^ 2) =
      (lo - s) * ((2 * m + lo * m ^ 2 - lo) * s + 1 + 2 * lo * m - m ^ 2) := by ring
  have hq : 0 ≤ (2 * m + lo * m ^ 2 - lo) * s + 1 + 2 * lo * m - m ^ 2 := by
    have em : (2 * m + lo * m ^ 2 - lo) * m + 1 + 2 * lo * m - m ^ 2 = (1 + m ^ 2) * (1 + lo * m) := by ring
    have el : (2 * m + lo * m ^ 2 - lo) * lo + 1 + 2 * lo * m - m ^ 2 = (1 - lo ^ 2) * (1 - m ^ 2) + 4 * lo * m := by
      ring
    have hlo1 : lo ≤ 1 := (hlos.trans hsm).trans hm1
    have A : 0 ≤ (1 + m ^ 2) * (1 + lo * m) := by positivity
    have B : 0 ≤ (1 - lo ^ 2) * (1 - m ^ 2) + 4 * lo * m := by
      have : 0 ≤ 1 - lo ^ 2 := by nlinarith
      have : 0 ≤ 1 - m ^ 2 := by nlinarith
      positivity
    rcases eq_or_lt_of_le (hlos.trans hsm) with heq | hlt
    · have : s = lo := le_antisymm (heq ▸ hsm) hlos
      rw [this, el]; exact B
    · have hne : m - lo ≠ 0 := by linarith
      have hθ : s = lo + (s - lo) / (m - lo) * (m - lo) := by rw [div_mul_cancel₀ _ hne]; ring
      have ht0 : 0 ≤ (s - lo) / (m - lo) := div_nonneg (sub_nonneg.mpr hlos) (by linarith)
      have ht1 : (s - lo) / (m - lo) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      set θ := (s - lo) / (m - lo)
      have : (2 * m + lo * m ^ 2 - lo) * s + 1 + 2 * lo * m - m ^ 2 =
          (1 - θ) * ((2 * m + lo * m ^ 2 - lo) * lo + 1 + 2 * lo * m - m ^ 2) +
            θ * ((2 * m + lo * m ^ 2 - lo) * m + 1 + 2 * lo * m - m ^ 2) := by
        rw [hθ]; ring
      rw [this, em, el]
      have := mul_nonneg (sub_nonneg.mpr ht1) B
      have := mul_nonneg ht0 A
      linarith
  have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlos) hq
  nlinarith [key]

/-- **Rotation ranges on a leaf.** For `0 ≤ lo ≤ m ≤ hi ≤ 1` and `s ∈ [lo, hi]`, the rotation from `u(m)` to `u(s)`
has `cos δ − 1 ∈ [−Cmax, 0]` and `|sin δ| ≤ Smax`, with the values at the endpoints. -/
theorem rot_range {lo m hi s : ℝ} (hlo0 : 0 ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hhi1 : hi ≤ 1)
    (hs : lo ≤ s ∧ s ≤ hi) :
    -(max (1 - (cu m * cu lo + su m * su lo)) (1 - (cu m * cu hi + su m * su hi))) ≤
        (cu m * cu s + su m * su s) - 1 ∧
      (cu m * cu s + su m * su s) - 1 ≤ 0 ∧
      |cu m * su s - su m * cu s| ≤
        max |cu m * su lo - su m * cu lo| |cu m * su hi - su m * cu hi| := by
  have hm1 : m ≤ 1 := hmhi.trans hhi1
  have hm0 : 0 ≤ m := hlo0.trans hlom
  refine ⟨?_, ?_, ?_⟩
  · rcases le_total s m with h | h
    · have := one_sub_dot_le_left hlo0 hm1 hs.1 h
      have := le_max_left (1 - (cu m * cu lo + su m * su lo)) (1 - (cu m * cu hi + su m * su hi))
      linarith
    · have := one_sub_dot_le_right hm0 hm1 h hs.2
      have := le_max_right (1 - (cu m * cu lo + su m * su lo)) (1 - (cu m * cu hi + su m * su hi))
      linarith
  · rw [dot_u]
    have := one_add_sq_pos s
    have := one_add_sq_pos m
    have : 0 ≤ 2 * (s - m) ^ 2 / ((1 + s ^ 2) * (1 + m ^ 2)) := by positivity
    linarith
  · rcases le_total s m with h | h
    · exact (det_le_left hlo0 hm1 hs.1 h).trans (le_max_left _ _)
    · exact (det_le_right hm0 hhi1 h hs.2).trans (le_max_right _ _)

end LebesgueCover
