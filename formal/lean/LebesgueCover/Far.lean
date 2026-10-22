import LebesgueCover.TreeSound
import LebesgueCover.VertTable

/-!
# The far region: a polygon fan around the disk and a far point

If a convex set contains the disk `D` and a point at distance `s ≥ g` from the centre, its area is at least the area
of a fan polygon: the far point followed by rational points of `D` (checked by `farPolyOK`). The polygon replaces
the arccos formula of the paper's corner lemma.
-/

open MeasureTheory Finset Complex

namespace LebesgueCover.Cert

/-- Rational vertices of the far polygon at distance `g`: `(g, 0)`, then `pts`. -/
def farQ (g : ℚ) (pts : List (ℚ × ℚ)) (j : ℕ) : ℚ × ℚ := if j = 0 then (g, 0) else pts.getD (j - 1) (0, 0)

/-- The far polygon with the far point at distance `s`. -/
noncomputable def farPt (s : ℝ) (pts : List (ℚ × ℚ)) (j : ℕ) : ℂ :=
  if j = 0 then (s : ℂ) else toC (castP (pts.getD (j - 1) (0, 0)))

/-- The check of the far polygon at distance `g` and target `τ`. -/
def farPolyOK (g τ : ℚ) (pts : List (ℚ × ℚ)) : Bool :=
  let M := pts.length + 1
  decide (2 ≤ pts.length) && decide (0 < g) &&
  (pts.all fun q => decide (dot2 q q ≤ 1 / 4)) &&
  decide (0 < (farQ g pts 1).2) && decide ((farQ g pts (M - 1)).2 < 0) &&
  ((List.range (M - 2)).all fun i => decide (0 < det2 (farQ g pts (i + 1)) (farQ g pts (i + 2)))) &&
  decide (((List.range M).map fun j => angleUB (farQ g pts j) (farQ g pts (nxt M j))).sum < 4 * (31415 / 10000)) &&
  decide (2 * τ < ((List.range M).map fun j => det2 (farQ g pts j) (farQ g pts (nxt M j))).sum)

lemma farPt_succ (s : ℝ) (pts : List (ℚ × ℚ)) (j : ℕ) : farPt s pts (j + 1) = toC (castP (farQ 0 pts (j + 1))) := by
  simp [farPt, farQ]

lemma farPt_g (g : ℚ) (pts : List (ℚ × ℚ)) (j : ℕ) : farPt (g : ℝ) pts j = toC (castP (farQ g pts j)) := by
  unfold farPt farQ
  split_ifs <;> apply Complex.ext <;> simp [toC, castP]

lemma farQ_succ (g g' : ℚ) (pts : List (ℚ × ℚ)) (j : ℕ) : farQ g pts (j + 1) = farQ g' pts (j + 1) := by
  simp [farQ]

lemma dot_le_disk {q : ℚ × ℚ} (h : dot2 q q ≤ 1 / 4) : toC (castP q) ∈ diskC := by
  rw [diskC, Metric.mem_closedBall, dist_zero_right, norm_toC]
  have h' : ((q.1 : ℝ)) ^ 2 + (q.2 : ℝ) ^ 2 ≤ 1 / 4 := by
    have := (Rat.cast_le (K := ℝ)).mpr h; push_cast [dot2] at this; nlinarith
  rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by simpa [castP] using h')

lemma nxt_last {M : ℕ} (hM : 0 < M) : nxt M (M - 1) = 0 := by
  unfold nxt; rw [Nat.sub_add_cancel hM, Nat.mod_self]

lemma nxt_lt {M j : ℕ} (hj : j + 1 < M) : nxt M j = j + 1 := by
  unfold nxt; exact Nat.mod_eq_of_lt hj

@[simp] lemma farQ_zero (g : ℚ) (pts : List (ℚ × ℚ)) : farQ g pts 0 = (g, 0) := by simp [farQ]
@[simp] lemma farPt_zero (s : ℝ) (pts : List (ℚ × ℚ)) : farPt s pts 0 = (s : ℂ) := by simp [farPt]

lemma farPt_pos (s : ℝ) (pts : List (ℚ × ℚ)) {j : ℕ} (hj : j ≠ 0) (g : ℚ) :
    farPt s pts j = toC (castP (farQ g pts j)) := by
  unfold farPt farQ; rw [if_neg hj, if_neg hj]

lemma getD_mem_of_lt {pts : List (ℚ × ℚ)} {i : ℕ} (hi : i < pts.length) : pts.getD i (0, 0) ∈ pts := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

/-- **Far polygon bound.** If the far polygon passes at distance `g`, every convex set containing the disk and a point
`s ≥ g` of the positive real axis has area `> τ`. -/
theorem far_poly {g τ : ℚ} {pts : List (ℚ × ℚ)} (h : farPolyOK g τ pts = true) {s : ℝ} (hs : (g : ℝ) ≤ s)
    {K : Set ℂ} (hK : Convex ℝ K) (hD : diskC ⊆ K) (hy : (s : ℂ) ∈ K) : ENNReal.ofReal τ < volume K := by
  simp only [farPolyOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, hg⟩, hdisk⟩, hy1⟩, hym⟩, hdets⟩, hang⟩, harea⟩ := h
  set M := pts.length + 1 with hM
  have hMpos : 0 < M := by omega
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hs0 : 0 < s := lt_of_lt_of_le hg0 hs
  set a := farPt s pts with ha
  set b := farPt (g : ℝ) pts with hb
  have hq1 : (0 : ℝ) < (farQ g pts 1).2 := by exact_mod_cast hy1
  have hqm : ((farQ g pts (M - 1)).2 : ℝ) < 0 := by exact_mod_cast hym
  -- the homotopy from the polygon at distance `g` to the polygon at distance `s`
  have hhom0 : ∀ t : ℝ, homC b a t 0 = (((1 - t) * g + t * s : ℝ) : ℂ) := by
    intro t; simp only [homC, ha, hb, farPt, if_pos rfl]; push_cast; ring
  have hhomj : ∀ t : ℝ, ∀ j, j ≠ 0 → homC b a t j = toC (castP (farQ g pts j)) := by
    intro t j hj
    simp only [homC, ha, hb]
    rw [farPt_pos s pts hj g, farPt_pos (g : ℝ) pts hj g]; push_cast; ring
  have hx : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (1 - t) * g + t * s := by
    intro t ⟨ht0, ht1⟩
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · simp [hs0]
    · nlinarith
  have hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j < M, 0 < detC (homC b a t j) (homC b a t (nxt M j)) := by
    intro t ht j hj
    by_cases h0 : j = 0
    · subst h0
      rw [nxt_lt (by omega : 0 + 1 < M), hhom0, hhomj t 1 one_ne_zero]
      simp only [detC, toC, castP, ofReal_re, ofReal_im]
      nlinarith [hx t ht]
    · by_cases hl : j = M - 1
      · rw [hl, nxt_last hMpos, hhom0, hhomj t (M - 1) (by omega)]
        simp only [detC, toC, castP, ofReal_re, ofReal_im]
        nlinarith [hx t ht]
      · rw [nxt_lt (by omega : j + 1 < M), hhomj t j h0, hhomj t (j + 1) (by omega), detC_toC, ← cast_det2]
        have := hdets (j - 1) (by omega)
        rw [show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega] at this
        exact_mod_cast this
  -- winding at distance `g`
  have hb0 : ∀ j < M, 0 < detC (b j) (b (nxt M j)) := fun j hj => by
    have := hdet 0 ⟨le_rfl, zero_le_one⟩ j hj; rwa [homC_zero] at this
  have h4 : turnSum b M < 4 * Real.pi := by
    have hsumR : ∑ j ∈ range M, ((angleUB (farQ g pts j) (farQ g pts (nxt M j)) : ℚ) : ℝ) < 4 * (31415 / 10000 : ℝ) := by
      have hc := (Rat.cast_lt (K := ℝ)).mpr hang
      rw [list_range_map_sum, Rat.cast_sum] at hc
      convert hc using 1; norm_num
    have hpi := Real.pi_gt_d4
    calc turnSum b M = ∑ j ∈ range M, Complex.arg (b (nxt M j) / b j) := rfl
      _ ≤ ∑ j ∈ range M, angleUBR (dotC (b j) (b (nxt M j))) (detC (b j) (b (nxt M j))) :=
          Finset.sum_le_sum fun j hj => arg_div_le_angleUBR (ne_zero_of_detC_pos (hb0 j (mem_range.mp hj)))
            (hb0 j (mem_range.mp hj))
      _ = ∑ j ∈ range M, ((angleUB (farQ g pts j) (farQ g pts (nxt M j)) : ℚ) : ℝ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [cast_angleUB, cast_dot2, cast_det2, hb, farPt_g, farPt_g, dotC_toC, detC_toC]
      _ < 4 * (31415 / 10000 : ℝ) := hsumR
      _ < 4 * Real.pi := by norm_num at hpi ⊢; linarith
  have hturn := wind_homotopy hMpos b a hdet h4
  have hwind : cum a M M = cum a M 0 + 2 * Real.pi := by rw [cum_m_eq, hturn]
  have ha_det : ∀ j < M, 0 < detC (a j) (a (nxt M j)) := fun j hj => by
    have := hdet 1 ⟨zero_le_one, le_rfl⟩ j hj; rwa [homC_one] at this
  have h0K : (0 : ℂ) ∈ K := hD (by simp [diskC])
  have hfan := fan_area_le hK hMpos h0K (a := a)
    (fun j hj => by
      rw [zero_add]
      by_cases h0 : j = 0
      · rw [h0, ha, farPt, if_pos rfl]; exact hy
      · rw [ha, farPt_pos s pts h0 g]
        apply hD
        apply dot_le_disk
        unfold farQ; rw [if_neg h0]
        exact hdisk _ (getD_mem_of_lt (by omega)))
    (fun j hj => ne_zero_of_detC_pos (ha_det j hj)) ha_det hwind
  -- the fan area grows with the distance
  have hge : ∑ j ∈ range M, ((det2 (farQ g pts j) (farQ g pts (nxt M j)) : ℚ) : ℝ) ≤
      ∑ j ∈ range M, detC (a j) (a (nxt M j)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := mem_range.mp hj
    rw [cast_det2]
    by_cases h0 : j = 0
    · subst h0
      have e1 : nxt M 0 = 1 := by rw [nxt_lt (by omega : 0 + 1 < M)]
      rw [e1, ha, farPt_pos s pts one_ne_zero g, farPt_zero, farQ_zero]
      simp only [det2R, detC, toC, castP, ofReal_re, ofReal_im]
      push_cast
      nlinarith
    · by_cases hl : j = M - 1
      · rw [hl, nxt_last hMpos, ha, farPt_pos s pts (by omega : M - 1 ≠ 0) g, farPt_zero, farQ_zero]
        simp only [det2R, detC, toC, castP, ofReal_re, ofReal_im]
        push_cast
        nlinarith
      · rw [nxt_lt (by omega : j + 1 < M), ha, farPt_pos s pts h0 g, farPt_pos s pts (by omega : j + 1 ≠ 0) g,
          detC_toC]
  have hareaR : 2 * (τ : ℝ) < ∑ j ∈ range M, ((det2 (farQ g pts j) (farQ g pts (nxt M j)) : ℚ) : ℝ) := by
    have hc := (Rat.cast_lt (K := ℝ)).mpr harea
    rw [list_range_map_sum, Rat.cast_sum] at hc
    push_cast at hc; exact hc
  have hpos : 0 < ∑ j ∈ range M, detC (a j) (a (nxt M j)) / 2 :=
    Finset.sum_pos (fun j hj => div_pos (ha_det j (mem_range.mp hj)) two_pos) ⟨0, mem_range.mpr hMpos⟩
  refine lt_of_lt_of_le ?_ hfan
  rw [ENNReal.ofReal_lt_ofReal_iff hpos, ← Finset.sum_div]
  linarith

/-- Multiplication by a unit complex number preserves area. -/
lemma volume_image_mul {w : ℂ} (hw : ‖w‖ = 1) (K : Set ℂ) : volume ((fun z => w * z) '' K) = volume K := by
  have e : (fun z => w * z) = linAB w (w * I) := by
    funext z; simp only [linAB, LinearMap.coe_mk, AddHom.coe_mk]
    conv_lhs => rw [← Complex.re_add_im z]
    ring
  rw [e, Measure.addHaar_image_linearMap, det_linAB]
  have hd : detC w (w * I) = 1 := by
    have h2 : w.re ^ 2 + w.im ^ 2 = 1 := by
      have := congrArg (· ^ 2) hw
      simp only [one_pow] at this
      rw [← this, Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [detC, mul_re, mul_im, I_re, I_im]; nlinarith
  rw [hd]; simp

/-- **Far point bound.** If the far polygon passes at distance `g`, every convex set containing the disk and a point
at distance `≥ g` from the centre has area `> τ`. -/
theorem far_point {g τ : ℚ} {pts : List (ℚ × ℚ)} (h : farPolyOK g τ pts = true) {K : Set ℂ} (hK : Convex ℝ K)
    (hD : diskC ⊆ K) {y : ℂ} (hy : y ∈ K) (hyg : (g : ℝ) ≤ ‖y‖) : ENNReal.ofReal τ < volume K := by
  have hg : (0 : ℝ) < g := by
    have h' := h
    simp only [farPolyOK, Bool.and_eq_true, decide_eq_true_eq] at h'
    exact_mod_cast h'.1.1.1.1.1.1.2
  have hyn : 0 < ‖y‖ := lt_of_lt_of_le hg hyg
  have hy0 : y ≠ 0 := norm_pos_iff.mp hyn
  set w : ℂ := (starRingEnd ℂ) y / (‖y‖ : ℂ) with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyn, div_self hyn.ne']
  have hwy : w * y = (‖y‖ : ℂ) := by
    have hn : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hyn.ne'
    rw [hw, div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) y) y, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    field_simp
    push_cast; ring
  set K' := (fun z => w * z) '' K with hK'
  have hcv : Convex ℝ K' := by
    have e : (fun z => w * z) = linAB w (w * I) := by
      funext z; simp only [linAB, LinearMap.coe_mk, AddHom.coe_mk]
      conv_lhs => rw [← Complex.re_add_im z]
      ring
    rw [hK', e]; exact hK.linear_image _
  have hD' : diskC ⊆ K' := by
    intro d hd
    refine ⟨(starRingEnd ℂ) w * d, hD ?_, ?_⟩
    · simp only [diskC, Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_conj, hwn, one_mul] at hd ⊢
      exact hd
    · show w * ((starRingEnd ℂ) w * d) = d
      rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hwn]; simp
  have hyK' : ((‖y‖ : ℝ) : ℂ) ∈ K' := ⟨y, hy, hwy⟩
  have := far_poly h hyg hcv hD' hyK'
  rwa [hK', volume_image_mul hwn] at this

/-! ## Vertices and the corner estimate -/

lemma vertC_eq (n l : ℕ) : vertC n l = (circR n : ℂ) * exp ((2 * Real.pi * l / n : ℝ) * I) := by
  apply Complex.ext
  · rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  · rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rfl

lemma circR_pos {n : ℕ} (hn : 2 ≤ n) : 0 < circR n := by
  unfold circR
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : Real.pi / (2 * n) < Real.pi / 2 := by
    rw [div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) (by norm_num)]; linarith
  have h2 : 0 < Real.cos (Real.pi / (2 * n)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, show 0 < Real.pi / (2 * n) by positivity], h1⟩
  positivity

lemma norm_exp_I (θ : ℝ) : ‖exp ((θ : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

lemma norm_vertC {n : ℕ} (hn : 2 ≤ n) (l : ℕ) : ‖vertC n l‖ = circR n := by
  rw [vertC_eq, norm_mul, norm_exp_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (circR_pos hn)]

/-- `cos (2πj/n) ≥ −cos(π/n)` for odd `n` and `j < n`. -/
lemma cos_vert_ge {n j : ℕ} (hn : Odd n) (hj : j < n) :
    -Real.cos (Real.pi / n) ≤ Real.cos (2 * Real.pi * j / n) := by
  have hn0 : (0 : ℝ) < n := by have := hn.pos; exact_mod_cast this
  rw [← Real.cos_pi_sub]
  obtain ⟨k, hk⟩ := hn
  by_cases h2 : 2 * j + 1 ≤ n
  · have h2r : (2 * j + 1 : ℝ) ≤ n := by exact_mod_cast h2
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · rw [sub_le_self_iff]; positivity
    · rw [div_le_iff₀ hn0, sub_mul, div_mul_cancel₀ _ hn0.ne']; nlinarith [Real.pi_pos]
  · have h3 : 2 * (n - j) + 1 ≤ n := by omega
    have h3r : (2 * ((n - j : ℕ) : ℝ) + 1 : ℝ) ≤ n := by exact_mod_cast h3
    have e : Real.cos (2 * Real.pi * j / n) = Real.cos (2 * Real.pi * (n - j : ℕ) / n) := by
      rw [Nat.cast_sub hj.le, show 2 * Real.pi * ((n : ℝ) - j) / n = 2 * Real.pi - 2 * Real.pi * j / n by
        field_simp]
      rw [Real.cos_two_pi_sub]
    rw [e]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · rw [sub_le_self_iff]; positivity
    · rw [div_le_iff₀ hn0, sub_mul, div_mul_cancel₀ _ hn0.ne']; nlinarith [Real.pi_pos]

/-- **The vertices lie in the Reuleaux polygon** (odd `n ≥ 3`). -/
theorem vert_mem {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) {l : ℕ} (hl : l < n) : vertC n l ∈ reuleauxC n := by
  simp only [reuleauxC, Set.mem_iInter, Metric.mem_closedBall, Finset.mem_range]
  intro m hm
  rw [dist_eq_norm]
  have hR := circR_pos (by omega : 2 ≤ n)
  -- ‖V_l − V_m‖² = 2R²(1 − cos(2π(l−m)/n)) ≤ 2R²(1 + cos(π/n)) = 1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h3
  set R := circR n
  have hc2 : 2 * R ^ 2 * (1 + Real.cos (Real.pi / n)) = 1 := by
    have hcos := Real.cos_sq (Real.pi / (2 * n))
    have e2 : 2 * (Real.pi / (2 * n)) = Real.pi / n := by field_simp
    rw [e2] at hcos
    have hc0 : 0 < Real.cos (Real.pi / (2 * n)) := by
      apply Real.cos_pos_of_mem_Ioo; constructor
      · linarith [show 0 < Real.pi / (2 * n) by positivity, Real.pi_pos]
      · rw [div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) (by norm_num)]; linarith
    have hRdef : R = 1 / (2 * Real.cos (Real.pi / (2 * n))) := rfl
    rw [hRdef]; field_simp; nlinarith [hcos]
  have hsq : ‖vertC n l - vertC n m‖ ^ 2 = 2 * R ^ 2 * (1 - Real.cos (2 * Real.pi * l / n - 2 * Real.pi * m / n)) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [vertC, sub_re, sub_im]
    rw [Real.cos_sub]
    have h1 := Real.sin_sq_add_cos_sq (2 * Real.pi * l / n)
    have h2 := Real.sin_sq_add_cos_sq (2 * Real.pi * m / n)
    linear_combination (R ^ 2) * h1 + (R ^ 2) * h2
  have hcos : -Real.cos (Real.pi / n) ≤ Real.cos (2 * Real.pi * l / n - 2 * Real.pi * m / n) := by
    rcases le_total m l with hml | hlm
    · have e : 2 * Real.pi * l / n - 2 * Real.pi * m / n = 2 * Real.pi * (l - m : ℕ) / n := by
        rw [Nat.cast_sub hml]; ring
      rw [e]; exact cos_vert_ge hn (by omega)
    · have e : 2 * Real.pi * l / n - 2 * Real.pi * m / n = -(2 * Real.pi * (m - l : ℕ) / n) := by
        rw [Nat.cast_sub hlm]; ring
      rw [e, Real.cos_neg]; exact cos_vert_ge hn (by omega)
  have hle : ‖vertC n l - vertC n m‖ ^ 2 ≤ 1 := by
    rw [hsq, ← hc2]; nlinarith [sq_nonneg R]
  nlinarith [norm_nonneg (vertC n l - vertC n m)]

/-- Some vertex direction is within `π/n` of any direction. -/
lemma exists_cos_ge {n : ℕ} (hn : 1 ≤ n) (φ : ℝ) :
    ∃ l < n, Real.cos (Real.pi / n) ≤ Real.cos (φ + 2 * Real.pi * l / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set l0 : ℤ := round (-φ * n / (2 * Real.pi)) with hl0
  have hr := abs_sub_round (-φ * n / (2 * Real.pi))
  rw [← hl0] at hr
  have hpi := Real.pi_pos
  -- |φ + 2π l0/n| ≤ π/n
  have hb : |φ + 2 * Real.pi * l0 / n| ≤ Real.pi / n := by
    have e : φ + 2 * Real.pi * l0 / n = -(2 * Real.pi / n) * (-φ * n / (2 * Real.pi) - l0) := by
      field_simp; ring
    rw [e, abs_mul, abs_neg, abs_of_pos (by positivity)]
    calc 2 * Real.pi / n * |-φ * n / (2 * Real.pi) - l0| ≤ 2 * Real.pi / n * (1 / 2) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = Real.pi / n := by ring
  set q : ℤ := l0 / n with hq
  set l : ℤ := l0 % n with hl
  have hl_nonneg : 0 ≤ l := Int.emod_nonneg _ (by exact_mod_cast (by omega : n ≠ 0))
  have hl_lt : l < n := Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : 0 < n))
  have hsplit : l0 = l + n * q := by have := Int.emod_add_ediv_mul l0 (n : ℤ); rw [hl, hq]; linarith
  refine ⟨l.toNat, by omega, ?_⟩
  have hlr : ((l.toNat : ℕ) : ℝ) = (l : ℝ) := by
    have := Int.toNat_of_nonneg hl_nonneg; exact_mod_cast this
  rw [hlr]
  have e2 : φ + 2 * Real.pi * l / n = (φ + 2 * Real.pi * l0 / n) - q * (2 * Real.pi) := by
    rw [hsplit]; push_cast; field_simp; ring
  rw [e2, Real.cos_sub_int_mul_two_pi, ← Real.cos_abs (φ + 2 * Real.pi * l0 / n)]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) _ hb
  have : Real.pi / n ≤ Real.pi := by
    rw [div_le_iff₀ hn0]; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  linarith

/-- **Corner estimate.** For a unit `u` and any `t`, some vertex `u V_l + t` of the placed Reuleaux polygon has
`|u V_l + t|² ≥ R² + |t|² + 2 R |t| cos(π/n)`. -/
theorem corner {n : ℕ} (hn : 3 ≤ n) {u t : ℂ} (hu : ‖u‖ = 1) :
    ∃ l < n, circR n ^ 2 + ‖t‖ ^ 2 + 2 * circR n * ‖t‖ * Real.cos (Real.pi / n) ≤ ‖u * vertC n l + t‖ ^ 2 := by
  have hR := circR_pos (by omega : 2 ≤ n)
  set R := circR n with hRdef
  by_cases ht : t = 0
  · refine ⟨0, by omega, ?_⟩
    subst ht
    rw [add_zero, norm_mul, hu, one_mul, norm_vertC (by omega), hRdef]
    simp
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  set v : ℂ := u * (starRingEnd ℂ) t / (‖t‖ : ℂ) with hv
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_div, norm_mul, hu, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htn]
    field_simp
  obtain ⟨l, hl, hcos⟩ := exists_cos_ge (by omega : 1 ≤ n) (Complex.arg v)
  refine ⟨l, hl, ?_⟩
  set φ : ℝ := Complex.arg v with hφ
  have hvexp : v = exp ((φ : ℂ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I v
    rw [hvn] at this; simpa using this.symm
  have hut : u * (starRingEnd ℂ) t = (‖t‖ : ℂ) * v := by
    rw [hv]; have : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast htn.ne'
    field_simp
  -- expand the square
  have hexp : ‖u * vertC n l + t‖ ^ 2 = R ^ 2 + ‖t‖ ^ 2 + 2 * (u * vertC n l * (starRingEnd ℂ) t).re := by
    rw [Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm, ← Complex.sq_norm, norm_mul, hu, one_mul,
      norm_vertC (by omega)]
  rw [hexp]
  have hre : (u * vertC n l * (starRingEnd ℂ) t).re = R * ‖t‖ * Real.cos (φ + 2 * Real.pi * l / n) := by
    rw [vertC_eq, show u * ((R : ℂ) * exp ((2 * Real.pi * l / n : ℝ) * I)) * (starRingEnd ℂ) t =
        (R : ℂ) * (u * (starRingEnd ℂ) t) * exp ((2 * Real.pi * l / n : ℝ) * I) by ring, hut, hvexp]
    rw [show (R : ℂ) * ((‖t‖ : ℂ) * exp ((φ : ℂ) * I)) * exp ((2 * Real.pi * l / n : ℝ) * I) =
        ((R * ‖t‖ : ℝ) : ℂ) * exp (((φ + 2 * Real.pi * l / n : ℝ) : ℂ) * I) by
      rw [show (((φ + 2 * Real.pi * l / n : ℝ) : ℂ)) * I = (φ : ℂ) * I + ((2 * Real.pi * l / n : ℝ) : ℂ) * I by
        push_cast; ring, Complex.exp_add]
      push_cast; ring]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [hre]
  have := mul_le_mul_of_nonneg_left hcos (by positivity : (0 : ℝ) ≤ 2 * R * ‖t‖)
  nlinarith

/-! ## The far region -/

open LebTrig LebTrig.Sound in
/-- Check that `g² ≤ R_n² + T² + 2 R_n T cos(π/n)` (lower ends of fixed-point enclosures of `R_n` and `cos(π/n)`). -/
def gCheck (n : ℕ) (T g : ℚ) : Bool :=
  let r := (encR n).1; let c := (cosPi 1 n).1
  decide (0 < n) && decide (0 < (cosPi 1 (2 * n)).1) && decide (0 ≤ r) && decide (0 ≤ c) && decide (0 ≤ T) &&
    decide (0 < g) &&
    decide (g ^ 2 * 2 ^ (2 * PR) ≤ (r : ℚ) ^ 2 + T ^ 2 * 2 ^ (2 * PR) + 2 * (r : ℚ) * T * (c : ℚ))

open LebTrig LebTrig.Sound in
lemma gCheck_sound {n : ℕ} {T g : ℚ} (h : gCheck n T g = true) {x : ℝ} (hx : (T : ℝ) ≤ x) :
    (g : ℝ) ^ 2 ≤ circR n ^ 2 + x ^ 2 + 2 * circR n * x * Real.cos (Real.pi / n) ∧ 0 < (g : ℝ) := by
  simp only [gCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hn, hc2⟩, hr⟩, hc⟩, hT⟩, hg⟩, hineq⟩ := h
  have hR := encR_encl hn hc2
  have hC := cosPi_encl 1 (b := n) hn
  have ea : ((1 : ℤ) : ℝ) * Real.pi / (n : ℝ) = Real.pi / n := by push_cast; ring
  rw [ea] at hC
  obtain ⟨hR1, -⟩ := hR
  obtain ⟨hC1, -⟩ := hC
  have hP : (0 : ℝ) < 2 ^ PR := by positivity
  set R := circR n; set C := Real.cos (Real.pi / n)
  set r : ℝ := ((encR n).1 : ℝ); set c : ℝ := ((cosPi 1 n).1 : ℝ)
  have hr0 : (0 : ℝ) ≤ r := by simp only [r]; exact_mod_cast hr
  have hc0 : (0 : ℝ) ≤ c := by simp only [c]; exact_mod_cast hc
  have hT0 : (0 : ℝ) ≤ T := by exact_mod_cast hT
  have hRlo : r / 2 ^ PR ≤ R := by rw [div_le_iff₀ hP]; linarith
  have hClo : c / 2 ^ PR ≤ C := by rw [div_le_iff₀ hP]; linarith
  have hineqR : (g : ℝ) ^ 2 * 2 ^ (2 * PR) ≤ r ^ 2 + (T : ℝ) ^ 2 * 2 ^ (2 * PR) + 2 * r * T * c := by
    have := (Rat.cast_le (K := ℝ)).mpr hineq; push_cast at this; exact this
  refine ⟨?_, by exact_mod_cast hg⟩
  have e2 : (2 : ℝ) ^ (2 * PR) = (2 ^ PR) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [e2] at hineqR
  have hP2 : (0 : ℝ) < (2 ^ PR) ^ 2 := by positivity
  have hg2 : (g : ℝ) ^ 2 ≤ (r / 2 ^ PR) ^ 2 + (T : ℝ) ^ 2 + 2 * (r / 2 ^ PR) * T * (c / 2 ^ PR) := by
    have e3 : (r / 2 ^ PR) ^ 2 + (T : ℝ) ^ 2 + 2 * (r / 2 ^ PR) * T * (c / 2 ^ PR) =
        (r ^ 2 + (T : ℝ) ^ 2 * (2 ^ PR) ^ 2 + 2 * r * T * c) / (2 ^ PR) ^ 2 := by
      field_simp
    rw [e3, le_div_iff₀ hP2]; linarith
  have hR0 : 0 ≤ R := le_trans (by positivity) hRlo
  have hx0 : 0 ≤ x := le_trans hT0 hx
  calc (g : ℝ) ^ 2 ≤ (r / 2 ^ PR) ^ 2 + (T : ℝ) ^ 2 + 2 * (r / 2 ^ PR) * T * (c / 2 ^ PR) := hg2
    _ ≤ R ^ 2 + x ^ 2 + 2 * R * x * C := by
      have h1 : (r / 2 ^ PR) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hRlo 2
      have h2 : (T : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hT0 hx 2
      have h3 : (r / 2 ^ PR) * T * (c / 2 ^ PR) ≤ R * x * C := by
        apply mul_le_mul (mul_le_mul hRlo hx hT0 hR0) hClo (by positivity) (by positivity)
      nlinarith

lemma rotAt_norm (p : ℕ → ℝ) (i : ℕ) : ‖toC (rotAt p i)‖ = 1 := by
  unfold rotAt
  split_ifs
  · rw [norm_toC]; simp
  · rw [norm_toC]
    have := cu_sq_add_su_sq (p (bS i))
    simp only [this, Real.sqrt_one]

/-- **Far region.** If body `i` is translated by at least `T_i`, every convex set containing the disk and the placed
bodies has area `> τ`. -/
theorem far_good {ns : List ℕ} {τ g : ℚ} {pts : List (ℚ × ℚ)} (hpoly : farPolyOK g τ pts = true)
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ ns.length) (hodd : Odd (ns.getD (i - 1) 0)) (h3 : 3 ≤ ns.getD (i - 1) 0)
    {T : ℚ} (hg : gCheck (ns.getD (i - 1) 0) T g = true) (p : ℕ → ℝ) (hfar : (T : ℝ) ≤ ‖toC (transAt p i)‖)
    {K : Set ℂ} (hK : Convex ℝ K) (hD : diskC ⊆ K)
    (hB : ∀ i, 1 ≤ i → i ≤ ns.length → ∀ q ∈ reuleauxC (ns.getD (i - 1) 0), placeC p i q ∈ K) :
    ENNReal.ofReal τ < volume K := by
  set n := ns.getD (i - 1) 0 with hn
  obtain ⟨l, hl, hcorner⟩ := corner h3 (rotAt_norm p i) (t := toC (transAt p i))
  obtain ⟨hg2, hg0⟩ := gCheck_sound hg hfar
  have hy : placeC p i (vertC n l) ∈ K := hB i hi1 hik _ (vert_mem hodd h3 hl)
  apply far_point hpoly hK hD hy
  have h2 : (g : ℝ) ^ 2 ≤ ‖placeC p i (vertC n l)‖ ^ 2 := le_trans hg2 (by simpa [placeC] using hcorner)
  exact (pow_le_pow_iff_left₀ hg0.le (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp h2

end LebesgueCover.Cert
