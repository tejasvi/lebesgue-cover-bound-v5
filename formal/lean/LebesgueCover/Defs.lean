import Mathlib

/-!
# Lebesgue's universal covering problem: definitions and statements

The plane is `EuclideanSpace ℝ (Fin 2)` with Mathlib's Lebesgue measure `volume`. A congruent copy of a set is its
image under an isometry `Plane ≃ᵢ Plane` (reflections allowed). `Metric.ediam` is the diameter with values in
`[0, ∞]` (unbounded sets have diameter `∞`).
-/

open MeasureTheory Set

namespace LebesgueCover

/-- The plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The point `(x, y)`. -/
def pt (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

/-- The disk `D` of diameter `1` centred at the origin. -/
def disk : Set Plane := Metric.closedBall 0 (1 / 2)

/-- `R_n = 1/(2 cos(π/(2n)))`. -/
noncomputable def circR (n : ℕ) : ℝ := 1 / (2 * Real.cos (Real.pi / (2 * n)))

/-- The vertices `V_{n,l} = R_n (cos(2πl/n), sin(2πl/n))`. -/
noncomputable def vert (n l : ℕ) : Plane :=
  pt (circR n * Real.cos (2 * Real.pi * l / n)) (circR n * Real.sin (2 * Real.pi * l / n))

/-- **Definition 2.1.** The regular Reuleaux `n`-gon of width `1`, `B_n = ⋂_{l<n} D(V_{n,l}, 1)`. -/
def reuleaux (n : ℕ) : Set Plane := ⋂ l ∈ Finset.range n, Metric.closedBall (vert n l) 1

/-- A universal cover: a convex set that contains a congruent copy of every set of diameter at most `1`. -/
def IsUniversalCover (Ω : Set Plane) : Prop :=
  Convex ℝ Ω ∧ ∀ S : Set Plane, Metric.ediam S ≤ 1 → ∃ φ : Plane ≃ᵢ Plane, φ '' S ⊆ Ω

/-- `Λ`: the infimum of the areas of universal covers. -/
noncomputable def lebesgueConstant : ENNReal := ⨅ (Ω : Set Plane) (_ : IsUniversalCover Ω), volume Ω

/-- `M(D, B₃, B₅)`: the least area of the convex hull of congruent copies of `D`, `B₃`, `B₅`. -/
noncomputable def hull3 : ENNReal :=
  ⨅ (g : Fin 3 → (Plane ≃ᵢ Plane)),
    volume (convexHull ℝ (g 0 '' disk ∪ g 1 '' reuleaux 3 ∪ g 2 '' reuleaux 5))

/-- `M(D, B₃, B₅, B₇)`. -/
noncomputable def hull4 : ENNReal :=
  ⨅ (g : Fin 4 → (Plane ≃ᵢ Plane)),
    volume (convexHull ℝ (g 0 '' disk ∪ g 1 '' reuleaux 3 ∪ g 2 '' reuleaux 5 ∪ g 3 '' reuleaux 7))

/-- The three-body bound `M(D, B₃, B₅) ≥ 0.8347`. -/
def Hull3Statement : Prop := ENNReal.ofReal (8347 / 10000) ≤ hull3

/-- The four-body bound `M(D, B₃, B₅, B₇) ≥ 0.836`. -/
def Hull4Statement : Prop := ENNReal.ofReal (836 / 1000) ≤ hull4

/-- `Λ ≥ 0.836`. -/
def MainStatement : Prop := ENNReal.ofReal (836 / 1000) ≤ lebesgueConstant

/-- The weakest reading of "universal cover" used in the paper: a convex `Ω` that contains a congruent copy
(reflections allowed) of every convex set of diameter exactly `1`. Every universal cover is such a cover, and so is
every cover in the reading with orientation-preserving copies only; a lower bound for these covers is therefore the
strongest form of the result. -/
def IsWeakUniversalCover (Ω : Set Plane) : Prop :=
  Convex ℝ Ω ∧ ∀ S : Set Plane, Convex ℝ S → Metric.ediam S = 1 → ∃ φ : Plane ≃ᵢ Plane, φ '' S ⊆ Ω

/-- `Λ ≥ 0.836` for the weaker notion of cover. -/
def WeakMainStatement : Prop :=
  ∀ Ω : Set Plane, IsWeakUniversalCover Ω → ENNReal.ofReal (836 / 1000) ≤ volume Ω

/-- `M(D, B₃, B₅, B₇, B₉)`. -/
noncomputable def hull5 : ENNReal :=
  ⨅ (g : Fin 5 → (Plane ≃ᵢ Plane)),
    volume (convexHull ℝ (g 0 '' disk ∪ g 1 '' reuleaux 3 ∪ g 2 '' reuleaux 5 ∪ g 3 '' reuleaux 7 ∪ g 4 '' reuleaux 9))

/-- The paper's Theorem 1.1, third bound: `M(D, B₃, B₅, B₇, B₉) ≥ 0.8366`. -/
def Hull5Statement : Prop := ENNReal.ofReal (8366 / 10000) ≤ hull5

/-- The consequence `Λ ≥ 0.8366`. -/
def Main5Statement : Prop := ENNReal.ofReal (8366 / 10000) ≤ lebesgueConstant

/-- `Λ ≥ 0.8366` for the weaker notion of cover. -/
def WeakMain5Statement : Prop :=
  ∀ Ω : Set Plane, IsWeakUniversalCover Ω → ENNReal.ofReal (8366 / 10000) ≤ volume Ω

/-- Non-vacuity: `Λ ≤ π` (the disk of radius `1` is a universal cover). -/
def NonVacuityStatement : Prop := lebesgueConstant ≤ ENNReal.ofReal Real.pi

end LebesgueCover
