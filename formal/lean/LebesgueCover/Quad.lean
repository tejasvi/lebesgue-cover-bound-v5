import Mathlib

/-!
# Lower bound of a quadratic on a box, with a diagonal-shift `LDLᵀ` certificate

For a symmetric `H` and a shift `σ ≥ 0` such that `H + diag σ` is positive semidefinite (certified by an exact
factorization `H + diag σ = L D Lᵀ` with `D ≥ 0`), every `y` in the box `|y − y₀| ≤ w` satisfies
`c + g·y + yᵀHy/2 ≥ c + g·y₀ + y₀ᵀHy₀/2 − Σ |g + H y₀|_a w_a − Σ σ_a w_a²/2`.
-/

open BigOperators

namespace LebesgueCover

variable {n : ℕ}

/-- The quadratic form `yᵀ H y`. -/
def qf (H : Fin n → Fin n → ℝ) (y : Fin n → ℝ) : ℝ := ∑ a, ∑ b, y a * H a b * y b

lemma qf_LDL {N L : Fin n → Fin n → ℝ} {D : Fin n → ℝ}
    (hN : ∀ a b, N a b = ∑ c, L a c * D c * L b c) (y : Fin n → ℝ) :
    qf N y = ∑ c, D c * (∑ a, y a * L a c) ^ 2 := by
  unfold qf
  have h1 : ∀ a b, y a * N a b * y b = ∑ c, D c * (y a * L a c) * (y b * L b c) := by
    intro a b
    rw [hN a b, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  have h2 : ∀ c, D c * (∑ a, y a * L a c) ^ 2 = ∑ a, ∑ b, D c * (y a * L a c) * (y b * L b c) := by
    intro c
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp_rw [h1, h2]
  calc ∑ a, ∑ b, ∑ c, D c * (y a * L a c) * (y b * L b c)
      = ∑ a, ∑ c, ∑ b, D c * (y a * L a c) * (y b * L b c) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, D c * (y a * L a c) * (y b * L b c) := Finset.sum_comm

/-- **PSD certificate.** -/
lemma qf_nonneg_of_LDL {N L : Fin n → Fin n → ℝ} {D : Fin n → ℝ} (hD : ∀ a, 0 ≤ D a)
    (hN : ∀ a b, N a b = ∑ c, L a c * D c * L b c) (y : Fin n → ℝ) : 0 ≤ qf N y := by
  rw [qf_LDL hN]
  exact Finset.sum_nonneg fun c _ => mul_nonneg (hD c) (sq_nonneg _)

lemma qf_add_shift (H : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (y : Fin n → ℝ) :
    qf (fun a b => H a b + if a = b then σ a else 0) y = qf H y + ∑ a, σ a * y a ^ 2 := by
  unfold qf
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Expansion of a symmetric quadratic form around `y₀`. -/
lemma qf_expand {H : Fin n → Fin n → ℝ} (hsymm : ∀ a b, H a b = H b a) (y y0 : Fin n → ℝ) :
    qf H y = qf H y0 + 2 * ∑ a, (∑ b, H a b * y0 b) * (y a - y0 a) + qf H (fun a => y a - y0 a) := by
  unfold qf
  have key : ∀ a b, y a * H a b * y b = y0 a * H a b * y0 b + H a b * y0 b * (y a - y0 a) +
      H a b * y0 a * (y b - y0 b) + (y a - y0 a) * H a b * (y b - y0 b) := by
    intro a b; ring
  simp_rw [key, Finset.sum_add_distrib]
  have e1 : ∑ a, ∑ b, H a b * y0 a * (y b - y0 b) = ∑ a, ∑ b, H a b * y0 b * (y a - y0 a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsymm b a]
  rw [e1]
  have e2 : ∑ a, (∑ b, H a b * y0 b) * (y a - y0 a) = ∑ a, ∑ b, H a b * y0 b * (y a - y0 a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
  rw [e2]
  ring

/-- **Quadratic lower bound on a box.** -/
theorem quad_box_lower {c : ℝ} {g y y0 w σ : Fin n → ℝ} {H : Fin n → Fin n → ℝ}
    (hsymm : ∀ a b, H a b = H b a) (hpsd : ∀ v, 0 ≤ qf H v + ∑ a, σ a * v a ^ 2) (hσ : ∀ a, 0 ≤ σ a)
    (hy : ∀ a, |y a - y0 a| ≤ w a) :
    c + ∑ a, g a * y0 a + qf H y0 / 2 - ∑ a, |g a + ∑ b, H a b * y0 b| * w a -
        (∑ a, σ a * w a ^ 2) / 2 ≤
      c + ∑ a, g a * y a + qf H y / 2 := by
  set Δ : Fin n → ℝ := fun a => y a - y0 a with hΔ
  have hexp := qf_expand hsymm y y0
  have hlin : -∑ a, |g a + ∑ b, H a b * y0 b| * w a ≤ ∑ a, (g a + ∑ b, H a b * y0 b) * Δ a := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 := hy a
    have h2 : -(|g a + ∑ b, H a b * y0 b| * |Δ a|) ≤ (g a + ∑ b, H a b * y0 b) * Δ a := by
      rw [← abs_mul]; exact neg_abs_le _
    have h3 : |g a + ∑ b, H a b * y0 b| * |Δ a| ≤ |g a + ∑ b, H a b * y0 b| * w a :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    linarith
  have hquad : -(∑ a, σ a * w a ^ 2) ≤ qf H Δ := by
    have h1 := hpsd Δ
    have h2 : ∑ a, σ a * Δ a ^ 2 ≤ ∑ a, σ a * w a ^ 2 := by
      refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hσ a)
      have := hy a
      have h0 : 0 ≤ w a := (abs_nonneg _).trans this
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    linarith
  have hgy : ∑ a, g a * y a = ∑ a, g a * y0 a + ∑ a, g a * Δ a := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun a _ => ?_; simp only [hΔ]; ring
  have hsplit : ∑ a, (g a + ∑ b, H a b * y0 b) * Δ a = ∑ a, g a * Δ a + ∑ a, (∑ b, H a b * y0 b) * Δ a := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun a _ => ?_; ring
  rw [hgy, hexp]
  nlinarith [hlin, hquad, hsplit]

end LebesgueCover
