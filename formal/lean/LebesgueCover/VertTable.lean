import LebesgueCover.Trig.TrigSound
import LebesgueCover.TreeSound
import LebFast.VT

/-!
# The vertex table

Rational approximations (numerators over `2^40`) of the Reuleaux vertices `V_{n,l} = R_n (cos(2πl/n), sin(2πl/n))`,
`R_n = 1/(2 cos(π/(2n)))`, for `n = 3, 5, 7, 9`, and the proof that each is within `2^-36` of the true vertex
(fixed-point enclosures of cosines and sines at rational multiples of `π`, evaluated by the kernel).
-/

open LebTrig LebTrig.Sound Real LebesgueCover.Fast

namespace LebesgueCover.Cert

/-- Enclosure (scale `2^PR`) of `R_n = 1/(2 cos(π/(2n)))`. -/
def encR (n : ℕ) : ℤ × ℤ :=
  let c := cosPi 1 (2 * n)
  (fdiv ((ONE : ℤ) * ONE) (2 * c.2.toNat), cdiv ((ONE : ℤ) * ONE) (2 * c.1.toNat))

/-- Check of one vertex: both coordinates within `2^-37`. -/
def vertCheck (n l : ℕ) : Bool :=
  let c := cosPi 1 (2 * n)
  let x := imulr (encR n) (cosPi (2 * l) n)
  let y := imulr (encR n) (sinPi (2 * l) n)
  let vx := (VT40 n l).1; let vy := (VT40 n l).2
  decide (0 < n) && decide (0 < c.1) && decide (vx * 2 ^ 88 - 2 ^ 91 ≤ x.1) && decide (x.2 ≤ vx * 2 ^ 88 + 2 ^ 91) &&
    decide (vy * 2 ^ 88 - 2 ^ 91 ≤ y.1) && decide (y.2 ≤ vy * 2 ^ 88 + 2 ^ 91)

lemma encR_encl {n : ℕ} (hn : 0 < n) (hc : 0 < (cosPi 1 (2 * n)).1) : Encl PR (encR n) (circR n) := by
  set c := cosPi 1 (2 * n) with hcdef
  have he := cosPi_encl 1 (b := 2 * n) (by omega)
  have hcos : cos ((1 : ℤ) * π / ((2 * n : ℕ) : ℝ)) = cos (π / (2 * n)) := by push_cast; ring_nf
  rw [hcos] at he
  obtain ⟨h1, h2⟩ := he
  set C := cos (π / (2 * n)) with hC
  have hP : (0 : ℝ) < 2 ^ PR := by positivity
  have hc1 : (0 : ℝ) < c.1 := by exact_mod_cast hc
  have hCpos : 0 < C := by
    have : (0 : ℝ) < 2 ^ PR * C := lt_of_lt_of_le hc1 h1
    exact pos_of_mul_pos_right this hP.le
  have hc2 : (0 : ℝ) < c.2 := lt_of_lt_of_le (lt_of_lt_of_le hc1 h1) h2
  have hc2n : ((c.2.toNat : ℕ) : ℝ) = c.2 := by
    have : 0 ≤ c.2 := by exact_mod_cast hc2.le
    exact_mod_cast Int.toNat_of_nonneg this
  have hc1n : ((c.1.toNat : ℕ) : ℝ) = c.1 := by
    have : 0 ≤ c.1 := hc.le
    exact_mod_cast Int.toNat_of_nonneg this
  have hR : circR n = 1 / (2 * C) := by rw [circR, hC]
  have hONE : (((ONE : ℤ) * ONE : ℤ) : ℝ) = 2 ^ PR * 2 ^ PR := by
    push_cast; rw [ONE_eq]
  unfold Encl encR
  rw [← hcdef]
  dsimp only
  constructor
  · -- lower end
    have hpos : 0 < 2 * c.2.toNat := by
      have : 0 < c.2.toNat := by
        have : (0 : ℝ) < (c.2.toNat : ℕ) := by rw [hc2n]; exact hc2
        exact_mod_cast this
      omega
    refine le_trans (fdiv_le _ hpos) ?_
    rw [hONE, hR]
    push_cast
    rw [hc2n, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  · have hpos : 0 < 2 * c.1.toNat := by
      have : 0 < c.1.toNat := by
        have : (0 : ℝ) < (c.1.toNat : ℕ) := by rw [hc1n]; exact hc1
        exact_mod_cast this
      omega
    refine le_trans ?_ (le_cdiv _ hpos)
    rw [hONE, hR]
    push_cast
    rw [hc1n, le_div_iff₀ (by positivity)]
    field_simp
    nlinarith

/-- **Vertex check soundness.** -/
lemma vertCheck_sound {n l : ℕ} (h : vertCheck n l = true) :
    |circR n * cos (2 * π * l / n) - ((VT40 n l).1 : ℝ) / 2 ^ 40| ≤ 1 / 2 ^ 37 ∧
      |circR n * sin (2 * π * l / n) - ((VT40 n l).2 : ℝ) / 2 ^ 40| ≤ 1 / 2 ^ 37 := by
  simp only [vertCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hn, hc⟩, hx1⟩, hx2⟩, hy1⟩, hy2⟩ := h
  have hR := encR_encl hn hc
  have hcos := cosPi_encl ((2 * l : ℕ) : ℤ) (b := n) hn
  have hsin := sinPi_encl ((2 * l : ℕ) : ℤ) (b := n) hn
  have ea : ((((2 * l : ℕ) : ℤ) : ℝ) * π / (n : ℝ)) = 2 * π * l / n := by push_cast; ring
  rw [ea] at hcos hsin
  have hX := imulr_encl hR hcos
  have hY := imulr_encl hR hsin
  have hP : (0 : ℝ) < 2 ^ PR := by positivity
  have hPR : (2 : ℝ) ^ PR = 2 ^ 88 * 2 ^ 40 := by unfold PR; norm_num
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  have cx1 : ((VT40 n l).1 : ℝ) * 2 ^ 88 - 2 ^ 91 ≤ ((imulr (encR n) (cosPi (2 * l) n)).1 : ℝ) := by exact_mod_cast hx1
  have cx2 : ((imulr (encR n) (cosPi (2 * l) n)).2 : ℝ) ≤ ((VT40 n l).1 : ℝ) * 2 ^ 88 + 2 ^ 91 := by exact_mod_cast hx2
  have cy1 : ((VT40 n l).2 : ℝ) * 2 ^ 88 - 2 ^ 91 ≤ ((imulr (encR n) (sinPi (2 * l) n)).1 : ℝ) := by exact_mod_cast hy1
  have cy2 : ((imulr (encR n) (sinPi (2 * l) n)).2 : ℝ) ≤ ((VT40 n l).2 : ℝ) * 2 ^ 88 + 2 ^ 91 := by exact_mod_cast hy2
  push_cast at hX1 hX2 hY1 hY2
  rw [hPR] at hX1 hX2 hY1 hY2
  constructor <;> rw [abs_le] <;> constructor <;> (
    rw [show (1 : ℝ) / 2 ^ 37 = 2 ^ 91 / (2 ^ 88 * 2 ^ 40) by norm_num]
    first
    | (rw [le_sub_iff_add_le, div_add_div_same, div_le_iff₀ (by positivity)] ; nlinarith)
    | (rw [sub_le_iff_le_add, div_add_div_same, le_div_iff₀ (by positivity)]; nlinarith)
    | (field_simp; nlinarith))

/-- The check passes at every vertex (kernel evaluation). -/
lemma vertCheck_all : ∀ n ∈ [3, 5, 7, 9], ∀ l < n, vertCheck n l = true := by decide

lemma VQ_cast (n l : ℕ) : toC (castP (VQ n l)) = ⟨((VT40 n l).1 : ℝ) / 2 ^ 40, ((VT40 n l).2 : ℝ) / 2 ^ 40⟩ := by
  apply Complex.ext <;> simp [toC, castP, VQ, Rat.mkRat_eq_div] <;> norm_num

/-- **The vertex table is correct** for `n = 3, 5, 7, 9` with `ν = 2^-36`. -/
theorem vertTable_ok {ns : List ℕ} (hns : ∀ n ∈ ns, n ∈ [3, 5, 7, 9]) : VertTableOK ns VQ (mkRat 1 (2 ^ 36)) := by
  refine ⟨by norm_num [Rat.mkRat_eq_div], by norm_num [Rat.mkRat_eq_div], fun n hn l hl => ?_⟩
  obtain ⟨hx, hy⟩ := vertCheck_sound (vertCheck_all n (hns n hn) l hl)
  rw [VQ_cast]
  have e : ((mkRat 1 (2 ^ 36) : ℚ) : ℝ) = 1 / 2 ^ 37 + 1 / 2 ^ 37 := by
    rw [Rat.mkRat_eq_div]; push_cast; norm_num
  rw [e]
  apply norm_sub_le_of_parts
  · simp only [vertC]; rw [abs_sub_comm]; exact hx
  · simp only [vertC]; rw [abs_sub_comm]; exact hy

end LebesgueCover.Cert
