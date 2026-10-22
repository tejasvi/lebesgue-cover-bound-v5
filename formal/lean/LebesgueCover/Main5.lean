import LebesgueCover.Reduce
import LebesgueCover.Far11Data
import LebFast.Root11

/-!
# `M(D, B₃, B₅, B₇, B₉) ≥ 0.8366` from the root box

The final reduction: every configuration of congruent copies is, after a common isometry, a placement in the
fundamental domain (`normal_form`); a placement with all translations in the root box is covered by the certificate
(`GoodBox` of the root box, proved by the certificate shards); every other placement has a body translated beyond the
root box and is covered by the far polygon (`far_good`).
-/

open MeasureTheory Set Complex LebesgueCover.Fast

namespace LebesgueCover.Cert

/-- Half-widths of the root box in the translations. -/
def T11 (i : ℕ) : ℚ := LebesgueCover.Far11.Ts.getD (i - 1) 0

lemma far11_tau : LebesgueCover.Far11.τ = tau11 := by
  simp [LebesgueCover.Far11.τ, tau11, Rat.mkRat_eq_div]

lemma toC_norm_ge {x y : ℝ} {T : ℝ} (h : T < |x| ∨ T < |y|) : T ≤ ‖toC (x, y)‖ := by
  rw [norm_toC]
  rcases h with h | h
  · have : |x| ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
    linarith
  · have : |y| ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
    linarith

/-- **`M(D, B₃, B₅, B₇, B₉) ≥ 0.8366`**, given that the root box is good (the certificate). -/
theorem hull5_of_root_good (hroot : GoodBox ns11 tau11 (fun i => rl11.getD i 0) (fun i => rh11.getD i 0)) :
    Hull5Statement := by
  unfold Hull5Statement hull5
  refine le_iInf fun g => ?_
  set U := g 0 '' disk ∪ g 1 '' reuleaux 3 ∪ g 2 '' reuleaux 5 ∪ g 3 '' reuleaux 7 ∪ g 4 '' reuleaux 9 with hU
  set S := convexHull ℝ U with hS
  rw [← volume_eC_image S]
  have hconv : Convex ℝ (eC '' S) := (convex_convexHull ℝ U).linear_image eC.toLinearEquiv.toLinearMap
  set h : Fin 5 → (ℂ ≃ᵢ ℂ) := fun i => (eC.symm.toIsometryEquiv).trans ((g i).trans eC.toIsometryEquiv) with hh
  have himg : ∀ i (B : Set Plane), h i '' (eC '' B) = eC '' (g i '' B) := by
    intro i B
    simp only [hh, Set.image_image, IsometryEquiv.trans_apply, LinearIsometryEquiv.coe_toIsometryEquiv,
      LinearIsometryEquiv.symm_apply_apply]
  have hsub : ∀ i (B : Set Plane), g i '' B ⊆ U → h i '' (eC '' B) ⊆ eC '' S := by
    intro i B hB
    rw [himg]
    exact Set.image_mono (hB.trans (subset_convexHull ℝ U))
  obtain ⟨p, hfund, K, hKc, hKvol, hKD, hK1, hK2, hK3, hK4⟩ := normal_form h hconv
    (by rw [← eC_disk]; exact hsub 0 disk (fun x hx => Or.inl (Or.inl (Or.inl (Or.inl hx)))))
    (by rw [← eC_reuleaux]; exact hsub 1 _ (fun x hx => Or.inl (Or.inl (Or.inl (Or.inr hx)))))
    (by rw [← eC_reuleaux]; exact hsub 2 _ (fun x hx => Or.inl (Or.inl (Or.inr hx))))
    (by rw [← eC_reuleaux]; exact hsub 3 _ (fun x hx => Or.inl (Or.inr hx)))
    (by rw [← eC_reuleaux]; exact hsub 4 _ (fun x hx => Or.inr hx))
  rw [← hKvol]
  have hτ : ENNReal.ofReal (8366 / 10000) = ENNReal.ofReal ((tau11 : ℚ) : ℝ) := by
    congr 1; simp [tau11, Rat.mkRat_eq_div]; norm_num
  rw [hτ]
  apply le_of_lt
  have hB : ∀ i, 1 ≤ i → i ≤ ns11.length → ∀ q ∈ reuleauxC (ns11.getD (i - 1) 0), placeC p i q ∈ K := by
    intro i hi1 hi4 q hq
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by simp [ns11] at hi4; omega
    rcases this with rfl | rfl | rfl | rfl
    · exact hK1 q (by simpa [ns11] using hq)
    · exact hK2 q (by simpa [ns11] using hq)
    · exact hK3 q (by simpa [ns11] using hq)
    · exact hK4 q (by simpa [ns11] using hq)
  by_cases hin : ∀ i, 1 ≤ i → i ≤ 4 → |p (bTx i)| ≤ T11 i ∧ |p (bTy i)| ≤ T11 i
  · refine hroot p (fun a ha => ?_) K hKc hKD hB
    obtain ⟨⟨h2a, h2b⟩, ⟨h3a, h3b⟩, ⟨h4a, h4b⟩⟩ := hfund
    have t5 := (tanCheck_sound tan5_ok).1
    have t7 := (tanCheck_sound tan7_ok).1
    have t9 := (tanCheck_sound tan9_ok).1
    push_cast at t5 t7 t9
    rw [show (1 : ℝ) * Real.pi / 10 = Real.pi / 10 by ring] at t5
    rw [show (1 : ℝ) * Real.pi / 7 = Real.pi / 7 by ring] at t7
    rw [show (1 : ℝ) * Real.pi / 9 = Real.pi / 9 by ring] at t9
    have b1 := hin 1 le_rfl (by norm_num)
    have b2 := hin 2 (by norm_num) (by norm_num)
    have b3 := hin 3 (by norm_num) (by norm_num)
    have b4 := hin 4 (by norm_num) (by norm_num)
    simp only [ns11, List.length_cons, List.length_nil] at ha
    simp only [bTx, bTy, bS, T11, LebesgueCover.Far11.Ts] at b1 b2 b3 b4 h2a h2b h3a h3b h4a h4b
    norm_num at b1 b2 b3 b4 h2a h2b h3a h3b h4a h4b
    simp only [abs_le] at b1 b2 b3 b4
    interval_cases a <;> simp [rl11, rh11, Rat.mkRat_eq_div] <;> norm_num <;>
      first | constructor <;> linarith | linarith
  · push Not at hin
    obtain ⟨i, hi1, hi4, hout⟩ := hin
    have hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    have hfar : (T11 i : ℝ) ≤ ‖toC (transAt p i)‖ := by
      simp only [transAt, if_neg (show i ≠ 0 by omega)]
      apply toC_norm_ge
      by_contra hc; push Not at hc
      exact absurd (hout hc.1) (not_lt.mpr hc.2)
    rw [← far11_tau]
    have hpoly := LebesgueCover.Far11.poly_ok
    have hg : gCheck (ns11.getD (i - 1) 0) (T11 i) LebesgueCover.Far11.g = true := by
      rcases hi with rfl | rfl | rfl | rfl
      · exact LebesgueCover.Far11.g3_ok
      · exact LebesgueCover.Far11.g5_ok
      · exact LebesgueCover.Far11.g7_ok
      · exact LebesgueCover.Far11.g9_ok
    have hodd : Odd (ns11.getD (i - 1) 0) := by
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
    have h3 : 3 ≤ ns11.getD (i - 1) 0 := by
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    have hik : i ≤ ns11.length := by simp [ns11]; omega
    exact far_good hpoly hi1 hik hodd h3 hg p hfar hKc hKD hB

end LebesgueCover.Cert
