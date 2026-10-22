import LebesgueCover.Defs

/-!
# Basic facts: non-vacuity (`Λ ≤ π`) and the implication between the two readings
-/

open MeasureTheory Set

namespace LebesgueCover

/-- Every universal cover is a weak universal cover. -/
theorem IsUniversalCover.weak {Ω : Set Plane} (h : IsUniversalCover Ω) : IsWeakUniversalCover Ω :=
  ⟨h.1, fun S _ hS => h.2 S hS.le⟩

/-- The strongest reading implies `Λ ≥ 0.836`. -/
theorem main_of_weak (h : WeakMainStatement) : MainStatement :=
  le_iInf₂ fun Ω hΩ => h Ω hΩ.weak

/-- The strongest reading implies `Λ ≥ 0.8366`. -/
theorem main5_of_weak5 (h : WeakMain5Statement) : Main5Statement :=
  le_iInf₂ fun Ω hΩ => h Ω hΩ.weak

/-- The closed disk of radius `1` is a universal cover. -/
theorem isUniversalCover_closedBall : IsUniversalCover (Metric.closedBall (0 : Plane) 1) := by
  refine ⟨convex_closedBall 0 1, fun S hS => ?_⟩
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨IsometryEquiv.refl _, by simp⟩
  · refine ⟨IsometryEquiv.addRight (-s₀), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, IsometryEquiv.addRight_apply, dist_zero_right, ← sub_eq_add_neg,
      ← dist_eq_norm]
    have h1 : edist x s₀ ≤ 1 := (Metric.edist_le_ediam_of_mem hx hs₀).trans hS
    rw [edist_dist] at h1
    exact (ENNReal.ofReal_le_one).mp h1

/-- **Non-vacuity:** `Λ ≤ π`. -/
theorem nonVacuity : NonVacuityStatement := by
  unfold NonVacuityStatement lebesgueConstant
  refine (iInf₂_le _ isUniversalCover_closedBall).trans ?_
  simp

end LebesgueCover
