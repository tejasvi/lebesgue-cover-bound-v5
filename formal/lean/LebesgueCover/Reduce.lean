import LebesgueCover.Far
import LebesgueCover.Defs
import LebesgueCover.VertTable

/-!
# From isometries of the plane to placements

The hull area of congruent copies of `D, B_{n_1}, …` is invariant under a common isometry. Isometries of `ℂ` are
`z ↦ a z + b` or `z ↦ a z̄ + b` with `|a| = 1`; the bodies are symmetric under `z ↦ z̄` and (for `B_n`) under the
rotation by `2π/n`. So every configuration is congruent to a placement with the disk at `0`, body 1 unrotated, and the
other rotation angles in the fundamental ranges, i.e. to a placement `p` in the coordinates of the certificate.
-/

open MeasureTheory Set Complex

namespace LebesgueCover.Cert

/-! ## The plane as `ℂ` -/

/-- The standard identification `ℝ² ≅ ℂ`, `(x, y) ↦ x + y i`. -/
noncomputable def eC : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

lemma eC_apply (x : Plane) : eC x = (x 0 : ℂ) + (x 1 : ℂ) * I := rfl

lemma eC_pt (x y : ℝ) : eC (pt x y) = ⟨x, y⟩ := by
  apply Complex.ext <;> simp [eC_apply, pt]

lemma eC_disk : eC '' disk = diskC := by
  ext z; constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [disk, Metric.mem_closedBall, dist_zero_right] at hx
    simp only [diskC, Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]; exact hx
  · intro hz
    refine ⟨eC.symm z, ?_, by simp⟩
    simp only [diskC, Metric.mem_closedBall, dist_zero_right] at hz
    simp only [disk, Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]; exact hz

lemma eC_vert (n l : ℕ) : eC (vert n l) = vertC n l := by
  rw [vert, eC_pt]; rfl

lemma eC_reuleaux (n : ℕ) : eC '' reuleaux n = reuleauxC n := by
  ext z; constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [reuleaux, Set.mem_iInter, Metric.mem_closedBall] at hx
    simp only [reuleauxC, Set.mem_iInter, Metric.mem_closedBall]
    intro l hl
    rw [← eC_vert, LinearIsometryEquiv.dist_map]; exact hx l hl
  · intro hz
    refine ⟨eC.symm z, ?_, by simp⟩
    simp only [reuleauxC, Set.mem_iInter, Metric.mem_closedBall] at hz
    simp only [reuleaux, Set.mem_iInter, Metric.mem_closedBall]
    intro l hl
    rw [← LinearIsometryEquiv.dist_map eC, eC_vert, LinearIsometryEquiv.apply_symm_apply]; exact hz l hl

/-- `eC` as a measurable equivalence. -/
noncomputable def eM : Plane ≃ᵐ ℂ := eC.toHomeomorph.toMeasurableEquiv

lemma eM_coe : (eM : Plane → ℂ) = eC := rfl

lemma volume_eC_image (S : Set Plane) : volume (eC '' S) = volume S := by
  have hf : MeasurePreserving eM := by rw [eM_coe]; exact LinearIsometryEquiv.measurePreserving eC
  rw [← eM_coe, MeasurableEquiv.image_eq_preimage_symm]
  exact (hf.symm eM).measure_preimage_equiv S

/-! ## Isometries of `ℂ` -/

/-- Every isometry of `ℂ` is `z ↦ a z + b` or `z ↦ a z̄ + b` with `|a| = 1`. -/
lemma iso_complex (h : ℂ ≃ᵢ ℂ) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ((∀ z, h z = a * z + b) ∨ (∀ z, h z = a * (starRingEnd ℂ) z + b)) := by
  set A := h.toRealAffineIsometryEquiv with hA
  set L := A.linearIsometryEquiv with hL
  have hdec : ∀ z, h z = L z + h 0 := by
    intro z
    have e := A.map_vadd 0 z
    simp only [vadd_eq_add, add_zero] at e
    rw [hA, IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at e
    rw [e]
  obtain ⟨a, ha⟩ := linear_isometry_complex L
  refine ⟨(a : ℂ), h 0, by simp, ?_⟩
  rcases ha with ha | ha
  · left; intro z; rw [hdec z, ha]; simp [rotation_apply]
  · right; intro z; rw [hdec z, ha]; simp [rotation_apply]

/-! ## Symmetries of the bodies -/

lemma conj_vertC {n : ℕ} (hn : 0 < n) {l : ℕ} (hl : l < n) :
    (starRingEnd ℂ) (vertC n l) = vertC n ((n - l) % n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · simp only [Nat.sub_zero, Nat.mod_self]
    apply Complex.ext <;> simp [vertC]
  · rw [Nat.mod_eq_of_lt (by omega : n - l < n)]
    apply Complex.ext
    · simp only [vertC, Complex.conj_re]
      congr 1
      rw [Nat.cast_sub hl.le, show 2 * Real.pi * ((n : ℝ) - l) / n = 2 * Real.pi - 2 * Real.pi * l / n by
        field_simp]
      rw [Real.cos_two_pi_sub]
    · simp only [vertC, Complex.conj_im]
      rw [Nat.cast_sub hl.le, show 2 * Real.pi * ((n : ℝ) - l) / n = 2 * Real.pi - 2 * Real.pi * l / n by
        field_simp]
      rw [Real.sin_two_pi_sub]; ring

/-- The disk and the Reuleaux polygons are symmetric under conjugation. -/
lemma conj_diskC : (starRingEnd ℂ) '' diskC = diskC := by
  ext z; constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [diskC, Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] at hw ⊢; exact hw
  · intro hz
    refine ⟨(starRingEnd ℂ) z, ?_, by simp⟩
    simp only [diskC, Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] at hz ⊢; exact hz

lemma mem_reuleauxC_conj {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z ∈ reuleauxC n) : (starRingEnd ℂ) z ∈ reuleauxC n := by
  simp only [reuleauxC, Set.mem_iInter, Metric.mem_closedBall, Finset.mem_range] at hz ⊢
  intro l hl
  have h := hz ((n - l) % n) (Nat.mod_lt _ hn)
  rw [← conj_vertC hn hl] at h
  rw [dist_eq_norm] at h ⊢
  rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
  exact h

lemma conj_reuleauxC {n : ℕ} (hn : 0 < n) : (starRingEnd ℂ) '' reuleauxC n = reuleauxC n := by
  ext z; constructor
  · rintro ⟨w, hw, rfl⟩; exact mem_reuleauxC_conj hn hw
  · intro hz; exact ⟨(starRingEnd ℂ) z, mem_reuleauxC_conj hn hz, by simp⟩

lemma exp_two_pi_int (n : ℕ) (hn : 0 < n) (m : ℤ) (x : ℝ) :
    exp (((x + 2 * Real.pi * (m * n) / n : ℝ) : ℂ) * I) = exp ((x : ℂ) * I) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have e : (x + 2 * Real.pi * (m * n) / n : ℝ) = x + m * (2 * Real.pi) := by field_simp
  rw [e, show ((x + m * (2 * Real.pi) : ℝ) : ℂ) * I = (x : ℂ) * I + m * (2 * Real.pi * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma mod_shift {n : ℕ} (hn : 0 < n) {l : ℕ} (hl : l < n) (k : ℕ) : ((l + (n - k % n)) % n + k) % n = l := by
  rw [Nat.mod_add_mod]
  have h1 := Nat.mod_add_div k n
  have h2 := Nat.mod_lt k hn
  have : l + (n - k % n) + k = l + n * (1 + k / n) := by
    zify [h2.le] at *
    linarith
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- Rotation by `2πk/n` permutes the vertices. -/
lemma rot_vertC {n : ℕ} (hn : 0 < n) (l k : ℕ) :
    exp (((2 * Real.pi * k / n : ℝ) : ℂ) * I) * vertC n l = vertC n ((l + k) % n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [vertC_eq, vertC_eq, mul_left_comm, ← Complex.exp_add]
  congr 1
  have hdiv := Nat.mod_add_div (l + k) n
  set r := (l + k) % n; set q := (l + k) / n
  have hlk : ((l : ℝ) + k) = r + n * q := by exact_mod_cast (by omega : l + k = r + n * q)
  have e1 : (2 * Real.pi * k / n + 2 * Real.pi * l / n : ℝ) = 2 * Real.pi * r / n + 2 * Real.pi * ((q : ℤ) * n) / n := by
    push_cast
    field_simp
    linear_combination hlk
  rw [show (((2 * Real.pi * k / n : ℝ) : ℂ) * I + ((2 * Real.pi * l / n : ℝ) : ℂ) * I) =
      (((2 * Real.pi * k / n + 2 * Real.pi * l / n : ℝ)) : ℂ) * I by push_cast; ring, e1, exp_two_pi_int n hn]

lemma mem_reuleauxC_rot {n : ℕ} (hn : 0 < n) (k : ℕ) {z : ℂ} (hz : z ∈ reuleauxC n) :
    exp (((2 * Real.pi * k / n : ℝ) : ℂ) * I) * z ∈ reuleauxC n := by
  simp only [reuleauxC, Set.mem_iInter, Metric.mem_closedBall, Finset.mem_range] at hz ⊢
  intro l hl
  set m := (l + (n - k % n)) % n with hm
  have hmn : m < n := Nat.mod_lt _ hn
  have hv : exp (((2 * Real.pi * k / n : ℝ) : ℂ) * I) * vertC n m = vertC n l := by
    rw [rot_vertC hn, hm, mod_shift hn hl]
  have h := hz m hmn
  rw [← hv, dist_eq_norm, ← mul_sub, norm_mul, norm_exp_I, one_mul, ← dist_eq_norm]
  exact h

/-! ## Angles -/

/-- A rotation of `B_n` brings any unit complex number to an angle in `[0, 2π/n)`. -/
lemma reduce_angle {n : ℕ} (hn : 1 ≤ n) {v : ℂ} (hv : ‖v‖ = 1) :
    ∃ k : ℕ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 2 * Real.pi / n ∧
      v * exp (((2 * Real.pi * k / n : ℝ) : ℂ) * I) = exp ((ρ : ℂ) * I) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpi := Real.pi_pos
  set φ := Complex.arg v with hφ
  have hvexp : v = exp ((φ : ℂ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I v
    rw [hv] at this; simpa using this.symm
  set m : ℤ := ⌊φ * n / (2 * Real.pi)⌋ with hm
  have hfl := Int.floor_le (φ * n / (2 * Real.pi))
  have hlt := Int.lt_floor_add_one (φ * n / (2 * Real.pi))
  rw [← hm] at hfl hlt
  set ρ := φ - 2 * Real.pi * m / n with hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, sub_nonneg, div_le_iff₀ hn0]
    rw [le_div_iff₀ (by positivity)] at hfl; nlinarith
  have hρ1 : ρ < 2 * Real.pi / n := by
    rw [hρ, sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hn0]
    rw [div_lt_iff₀ (by positivity)] at hlt; nlinarith
  set k : ℤ := (-m) % n with hk
  have hk0 : 0 ≤ k := Int.emod_nonneg _ (by exact_mod_cast (by omega : n ≠ 0))
  have hsplit : -m = k + n * ((-m) / n) := by have := Int.emod_add_ediv_mul (-m) (n : ℤ); rw [hk]; linarith
  refine ⟨k.toNat, ρ, hρ0, hρ1, ?_⟩
  have hkr : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by have := Int.toNat_of_nonneg hk0; exact_mod_cast this
  rw [hkr, hvexp, ← Complex.exp_add]
  have e : (φ : ℂ) * I + ((2 * Real.pi * k / n : ℝ) : ℂ) * I =
      ((ρ + 2 * Real.pi * ((((-m) / n : ℤ) : ℝ) * (-1) * n) / n : ℝ) : ℂ) * I + 0 := by
    have hkm : (k : ℝ) = -m - n * (((-m) / n : ℤ) : ℝ) := by
      have := congrArg (fun x : ℤ => (x : ℝ)) hsplit; push_cast at this; linarith
    rw [add_zero, hρ, hkm]; push_cast; field_simp; ring
  rw [e, add_zero]
  have := exp_two_pi_int n (by omega) (-((-m) / n)) ρ
  push_cast at this ⊢
  rw [← this]; congr 2; ring

/-- The half-angle parametrization. -/
lemma half_angle {ρ : ℝ} (h1 : -Real.pi < ρ) (h2 : ρ < Real.pi) :
    toC (cu (Real.tan (ρ / 2)), su (Real.tan (ρ / 2))) = exp ((ρ : ℂ) * I) := by
  have hc : 0 < Real.cos (ρ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsc := Real.sin_sq_add_cos_sq (ρ / 2)
  have hcos : Real.cos ρ = 2 * Real.cos (ρ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (ρ / 2); rw [show 2 * (ρ / 2) = ρ by ring] at h; exact h
  have hsin : Real.sin ρ = 2 * Real.sin (ρ / 2) * Real.cos (ρ / 2) := by
    have h := Real.sin_two_mul (ρ / 2); rw [show 2 * (ρ / 2) = ρ by ring] at h; exact h
  have hinv : (1 + Real.tan (ρ / 2) ^ 2)⁻¹ = Real.cos (ρ / 2) ^ 2 := Real.inv_one_add_tan_sq hc.ne'
  have htan : Real.tan (ρ / 2) * Real.cos (ρ / 2) = Real.sin (ρ / 2) := by
    rw [Real.tan_eq_sin_div_cos]; field_simp
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    simp only [toC, cu]
    rw [div_eq_mul_inv, hinv, hcos]
    have : Real.tan (ρ / 2) ^ 2 * Real.cos (ρ / 2) ^ 2 = Real.sin (ρ / 2) ^ 2 := by rw [← htan]; ring
    nlinarith
  · rw [Complex.exp_ofReal_mul_I_im]
    simp only [toC, su]
    rw [div_eq_mul_inv, hinv, hsin, ← htan]; ring

lemma tan_half_bounds {n : ℕ} (hn : 3 ≤ n) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 2 * Real.pi / n) :
    0 ≤ Real.tan (ρ / 2) ∧ Real.tan (ρ / 2) ≤ Real.tan (Real.pi / n) := by
  have hn0 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have hπn : Real.pi / n < Real.pi / 2 := by
    rw [div_lt_div_iff_of_pos_left hpi (by linarith) (by norm_num)]; linarith
  have hρ2 : ρ / 2 ≤ Real.pi / n := by
    rw [show 2 * Real.pi / n = 2 * (Real.pi / n) by ring] at h1; linarith
  refine ⟨Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith), ?_⟩
  rcases eq_or_lt_of_le hρ2 with heq | hlt
  · rw [heq]
  · exact (Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) hπn hlt).le

/-! ## Rational bounds for the rotation ranges -/

open LebTrig LebTrig.Sound in
/-- Check `tan(aπ/b) ≤ S` from fixed-point enclosures of `sin` and `cos`. -/
def tanCheck (a b : ℕ) (S : ℚ) : Bool :=
  let c := (cosPi (a : ℤ) b).1; let sn := (sinPi (a : ℤ) b).2
  decide (0 < b) && decide (0 < c) && decide (0 ≤ S) && decide ((sn : ℚ) ≤ S * (c : ℚ))

open LebTrig LebTrig.Sound in
lemma tanCheck_sound {a b : ℕ} {S : ℚ} (h : tanCheck a b S = true) :
    Real.tan (a * Real.pi / b) ≤ S ∧ 0 < Real.cos (a * Real.pi / b) := by
  simp only [tanCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hb, hc⟩, hS⟩, hle⟩ := h
  have hC := cosPi_encl (a : ℤ) (b := b) hb
  have hSn := sinPi_encl (a : ℤ) (b := b) hb
  have ea : ((a : ℤ) : ℝ) * Real.pi / (b : ℝ) = a * Real.pi / b := by push_cast; ring
  rw [ea] at hC hSn
  obtain ⟨hC1, -⟩ := hC
  obtain ⟨-, hS2⟩ := hSn
  have hP : (0 : ℝ) < 2 ^ PR := by positivity
  have hc0 : (0 : ℝ) < ((cosPi (a : ℤ) b).1 : ℝ) := by exact_mod_cast hc
  have hcos : 0 < Real.cos (a * Real.pi / b) := by
    have : (0 : ℝ) < 2 ^ PR * Real.cos (a * Real.pi / b) := lt_of_lt_of_le hc0 hC1
    exact pos_of_mul_pos_right this hP.le
  refine ⟨?_, hcos⟩
  have hleR : (((sinPi (a : ℤ) b).2 : ℤ) : ℝ) ≤ (S : ℝ) * ((cosPi (a : ℤ) b).1 : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hle; push_cast at this; exact this
  have hS0 : (0 : ℝ) ≤ S := by exact_mod_cast hS
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos]
  have : 2 ^ PR * Real.sin (a * Real.pi / b) ≤ 2 ^ PR * ((S : ℝ) * Real.cos (a * Real.pi / b)) := by
    calc 2 ^ PR * Real.sin (a * Real.pi / b) ≤ (((sinPi (a : ℤ) b).2 : ℤ) : ℝ) := hS2
      _ ≤ (S : ℝ) * ((cosPi (a : ℤ) b).1 : ℝ) := hleR
      _ ≤ (S : ℝ) * (2 ^ PR * Real.cos (a * Real.pi / b)) := mul_le_mul_of_nonneg_left hC1 hS0
      _ = 2 ^ PR * ((S : ℝ) * Real.cos (a * Real.pi / b)) := by ring
  exact le_of_mul_le_mul_left this hP

theorem tan5_ok : tanCheck 1 10 (333 / 1024) = true := by decide +kernel
theorem tan7_ok : tanCheck 1 7 (1973 / 4096) = true := by decide +kernel
theorem tan9_ok : tanCheck 1 9 (1491 / 4096) = true := by decide +kernel

/-! ## Flags: identity or conjugation -/

/-- `z` or `z̄`. -/
def flipC (ε : Bool) (z : ℂ) : ℂ := if ε then (starRingEnd ℂ) z else z

@[simp] lemma flip_flip (ε : Bool) (z : ℂ) : flipC ε (flipC ε z) = z := by cases ε <;> simp [flipC]
lemma flip_mul (ε : Bool) (a b : ℂ) : flipC ε (a * b) = flipC ε a * flipC ε b := by cases ε <;> simp [flipC]
lemma flip_add (ε : Bool) (a b : ℂ) : flipC ε (a + b) = flipC ε a + flipC ε b := by cases ε <;> simp [flipC]
lemma flip_sub (ε : Bool) (a b : ℂ) : flipC ε (a - b) = flipC ε a - flipC ε b := by cases ε <;> simp [flipC]
lemma norm_flip (ε : Bool) (z : ℂ) : ‖flipC ε z‖ = ‖z‖ := by cases ε <;> simp [flipC]
lemma flip_flip' (ε δ : Bool) (z : ℂ) : flipC ε (flipC δ z) = flipC (xor ε δ) z := by
  cases ε <;> cases δ <;> simp [flipC]

lemma mem_reuleauxC_flip {n : ℕ} (hn : 0 < n) (ε : Bool) {z : ℂ} (hz : z ∈ reuleauxC n) : flipC ε z ∈ reuleauxC n := by
  cases ε
  · simpa [flipC] using hz
  · simpa [flipC] using mem_reuleauxC_conj hn hz

lemma mem_diskC_of_norm {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : z ∈ diskC := by
  simpa [diskC, Metric.mem_closedBall, dist_zero_right] using hz

/-- **One body.** If `v ω^k = e^{iρ}` (`ω = e^{2πi/n}`), then every point `e^{iρ} z + t` with `z ∈ B_n` is a value of
`w ↦ v · flipC(w) + t` on `B_n`. -/
lemma body_hits {n : ℕ} (hn : 0 < n) {v t : ℂ} {k : ℕ} {ρ : ℝ} (ε : Bool)
    (hv : v * exp (((2 * Real.pi * k / n : ℝ) : ℂ) * I) = exp ((ρ : ℂ) * I)) {z : ℂ} (hz : z ∈ reuleauxC n) :
    ∃ w ∈ reuleauxC n, v * flipC ε w + t = exp ((ρ : ℂ) * I) * z + t := by
  refine ⟨flipC ε (exp (((2 * Real.pi * k / n : ℝ) : ℂ) * I) * z),
    mem_reuleauxC_flip hn ε (mem_reuleauxC_rot hn k hz), ?_⟩
  rw [flip_flip, ← mul_assoc, hv]

/-- The conjugate of a reduced unit gives the reflected angle `2π/n − ρ`. -/
lemma conj_reduce {n : ℕ} (hn : 1 ≤ n) {v : ℂ} {k : ℕ} {ρ : ℝ}
    (hv : v * exp (((2 * Real.pi * k / n : ℝ) : ℂ) * I) = exp ((ρ : ℂ) * I)) :
    ∃ k' : ℕ, (starRingEnd ℂ) v * exp (((2 * Real.pi * k' / n : ℝ) : ℂ) * I) =
      exp (((2 * Real.pi / n - ρ : ℝ) : ℂ) * I) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  -- conj v = e^{-iρ} e^{2πik/n}
  have hc : (starRingEnd ℂ) v = exp (((-ρ : ℝ) : ℂ) * I) * exp (((2 * Real.pi * k / n : ℝ) : ℂ) * I) := by
    have h1 := congrArg (starRingEnd ℂ) hv
    rw [map_mul, ← Complex.exp_conj, ← Complex.exp_conj] at h1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at h1
    have h2 : (starRingEnd ℂ) v = (starRingEnd ℂ) v * exp (((2 * Real.pi * k / n : ℝ) : ℂ) * -I) *
        exp (((2 * Real.pi * k / n : ℝ) : ℂ) * I) := by
      rw [mul_assoc, ← Complex.exp_add]; simp
    rw [h2, h1]; push_cast; ring_nf
  refine ⟨n + 1 - k % n, ?_⟩
  rw [hc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  have hk := Nat.mod_lt k (by omega : 0 < n)
  have hdiv := Nat.mod_add_div k n
  have hsum : ((k : ℝ) + ((n + 1 - k % n : ℕ) : ℝ)) = 1 + ((k / n + 1 : ℕ) : ℝ) * n := by
    have : k + (n + 1 - k % n) = 1 + (k / n + 1) * n := by
      zify [show k % n ≤ n + 1 by omega] at *
      nlinarith
    exact_mod_cast this
  have hreal : (-ρ + (2 * Real.pi * k / n + 2 * Real.pi * ((n + 1 - k % n : ℕ) : ℝ) / n) : ℝ) =
      (2 * Real.pi / n - ρ) + 2 * Real.pi * (((k / n + 1 : ℕ) : ℝ) * n) / n := by
    have e1 : 2 * Real.pi * k / n + 2 * Real.pi * ((n + 1 - k % n : ℕ) : ℝ) / n =
        2 * Real.pi * ((k : ℝ) + ((n + 1 - k % n : ℕ) : ℝ)) / n := by ring
    rw [e1, hsum]; field_simp; ring
  have e : ((-ρ : ℝ) : ℂ) * I + (((2 * Real.pi * k / n : ℝ) : ℂ) * I + ((2 * Real.pi * (n + 1 - k % n : ℕ) / n : ℝ) : ℂ) * I)
      = ((((2 * Real.pi / n - ρ) + 2 * Real.pi * ((((k / n + 1 : ℕ) : ℤ) : ℝ) * n) / n : ℝ)) : ℂ) * I := by
    rw [Int.cast_natCast, ← hreal]
    simp only [Complex.ofReal_add, Complex.ofReal_neg]
    ring
  rw [e, exp_two_pi_int n (by omega)]

/-! ## The normalizing isometry -/

/-- `z ↦ flipC ε (c (z − b))`. -/
def Phi (ε : Bool) (c b : ℂ) (z : ℂ) : ℂ := flipC ε (c * (z - b))

/-- Conjugation as a measurable equivalence. -/
noncomputable def conjM : ℂ ≃ᵐ ℂ := Complex.conjLIE.toHomeomorph.toMeasurableEquiv

lemma conj_volume (S : Set ℂ) : volume ((starRingEnd ℂ) '' S) = volume S := by
  have hf : MeasurePreserving conjM := LinearIsometryEquiv.measurePreserving Complex.conjLIE
  have e : ((starRingEnd ℂ) : ℂ → ℂ) = conjM := rfl
  rw [e, MeasurableEquiv.image_eq_preimage_symm]
  exact (hf.symm conjM).measure_preimage_equiv S

lemma flipC_false : flipC false = id := by funext z; simp [flipC]
lemma flipC_true : flipC true = ((starRingEnd ℂ) : ℂ → ℂ) := by funext z; simp [flipC]

lemma flip_volume (ε : Bool) (S : Set ℂ) : volume (flipC ε '' S) = volume S := by
  cases ε
  · rw [flipC_false, Set.image_id]
  · rw [flipC_true]; exact conj_volume S

lemma sub_volume (b : ℂ) (S : Set ℂ) : volume ((fun z => z - b) '' S) = volume S := by
  have e : (fun z : ℂ => z - b) '' S = (fun z => z + b) ⁻¹' S := by
    ext z; simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨w, hw, rfl⟩; simpa using hw
    · intro hz; exact ⟨z + b, hz, by ring⟩
  rw [e, measure_preimage_add_right]

lemma Phi_image (ε : Bool) (c b : ℂ) (S : Set ℂ) :
    Phi ε c b '' S = flipC ε '' ((fun z => c * z) '' ((fun z => z - b) '' S)) := by
  simp only [Set.image_image]; rfl

lemma Phi_volume {c : ℂ} (hc : ‖c‖ = 1) (ε : Bool) (b : ℂ) (S : Set ℂ) : volume (Phi ε c b '' S) = volume S := by
  rw [Phi_image, flip_volume, volume_image_mul hc, sub_volume]

lemma mul_eq_linAB (c : ℂ) : (fun z => c * z) = linAB c (c * I) := by
  funext z; simp only [linAB, LinearMap.coe_mk, AddHom.coe_mk]
  conv_lhs => rw [← Complex.re_add_im z]
  ring

lemma Phi_convex (ε : Bool) (c b : ℂ) {S : Set ℂ} (hS : Convex ℝ S) : Convex ℝ (Phi ε c b '' S) := by
  rw [Phi_image]
  have h1 : Convex ℝ ((fun z => z - b) '' S) := by
    have := hS.translate (-b)
    convert this using 2; ring
  have h2 : Convex ℝ ((fun z => c * z) '' ((fun z => z - b) '' S)) := by
    rw [mul_eq_linAB]; exact h1.linear_image _
  cases ε
  · rw [flipC_false, Set.image_id]; exact h2
  · have e : flipC true = (Complex.conjLIE.toLinearEquiv.toLinearMap : ℂ → ℂ) := by
      funext z; simp [flipC]
    rw [e]
    exact h2.linear_image _

lemma iso_flip (h : ℂ ≃ᵢ ℂ) : ∃ a b : ℂ, ‖a‖ = 1 ∧ ∃ σ : Bool, ∀ z, h z = a * flipC σ z + b := by
  obtain ⟨a, b, ha, h1 | h1⟩ := iso_complex h
  · exact ⟨a, b, ha, false, fun z => by simp [flipC, h1 z]⟩
  · exact ⟨a, b, ha, true, fun z => by simp [flipC, h1 z]⟩

lemma Phi_comp (ε σ : Bool) (c a b b0 w : ℂ) :
    Phi ε c b0 (a * flipC σ w + b) = flipC ε (c * a) * flipC (xor ε σ) w + flipC ε (c * (b - b0)) := by
  unfold Phi
  rw [show c * (a * flipC σ w + b - b0) = c * a * flipC σ w + c * (b - b0) by ring, flip_add, flip_mul,
    flip_flip']

/-! ## Placements from translations and rotation parameters -/

/-- The placement with translations `t i` (body `i ≥ 1`) and rotation parameters `s i` (body `i ≥ 2`). -/
noncomputable def mkPlace (t : ℕ → ℂ) (s : ℕ → ℝ) : ℕ → ℝ := fun a =>
  if a = 0 then (t 1).re else if a = 1 then (t 1).im else
  if a % 3 = 2 then s ((a + 4) / 3) else if a % 3 = 0 then (t ((a + 4) / 3)).re else (t ((a + 4) / 3)).im

lemma mkPlace_tx (t : ℕ → ℂ) (s : ℕ → ℝ) {i : ℕ} (hi : 2 ≤ i) : mkPlace t s (3 * i - 3) = (t i).re := by
  have h1 : (3 * i - 3 + 4) / 3 = i := by omega
  simp only [mkPlace]
  split_ifs <;> first | omega | rw [h1]

lemma mkPlace_ty (t : ℕ → ℂ) (s : ℕ → ℝ) {i : ℕ} (hi : 2 ≤ i) : mkPlace t s (3 * i - 2) = (t i).im := by
  have h1 : (3 * i - 2 + 4) / 3 = i := by omega
  simp only [mkPlace]
  split_ifs <;> first | omega | rw [h1]

lemma mkPlace_s (t : ℕ → ℂ) (s : ℕ → ℝ) {i : ℕ} (hi : 2 ≤ i) : mkPlace t s (bS i) = s i := by
  have h0 : ¬ (3 * i - 4 = 0) := by omega
  have h1 : ¬ (3 * i - 4 = 1) := by omega
  have h2 : (3 * i - 4) % 3 = 2 := by omega
  have h3 : (3 * i - 4 + 4) / 3 = i := by omega
  simp only [mkPlace, bS, h0, h1, h2, h3, if_false, if_true]

lemma mkPlace_trans (t : ℕ → ℂ) (s : ℕ → ℝ) {i : ℕ} (hi : 1 ≤ i) : toC (transAt (mkPlace t s) i) = t i := by
  unfold transAt
  rw [if_neg (by omega)]
  rcases Nat.lt_or_ge i 2 with h | h
  · have : i = 1 := by omega
    subst this
    apply Complex.ext <;> simp [toC, mkPlace, bTx, bTy]
  · have ex : bTx i = 3 * i - 3 := by simp [bTx]; omega
    have ey : bTy i = 3 * i - 2 := by simp [bTy]; omega
    apply Complex.ext
    · simp only [toC]; rw [ex, mkPlace_tx t s h]
    · simp only [toC]; rw [ey, mkPlace_ty t s h]

lemma placeC_mk1 (t : ℕ → ℂ) (s : ℕ → ℝ) (q : ℂ) : placeC (mkPlace t s) 1 q = q + t 1 := by
  rw [placeC, mkPlace_trans t s le_rfl]
  simp only [rotAt, toC, show (1 : ℕ) ≤ 1 from le_rfl, if_true]
  rw [show (⟨1, 0⟩ : ℂ) = 1 from Complex.ext rfl rfl, one_mul]

lemma placeC_mk {t : ℕ → ℂ} {s : ℕ → ℝ} {i : ℕ} (hi : 2 ≤ i) {ρ : ℝ} (hρ1 : -Real.pi < ρ) (hρ2 : ρ < Real.pi)
    (hs : s i = Real.tan (ρ / 2)) (q : ℂ) :
    placeC (mkPlace t s) i q = exp ((ρ : ℂ) * I) * q + t i := by
  rw [placeC, mkPlace_trans t s (by omega)]
  congr 2
  simp only [rotAt]
  rw [if_neg (by omega), mkPlace_s t s hi, hs, half_angle hρ1 hρ2]

/-! ## The normal form -/

/-- Placements in the fundamental domain for `D, B₃, B₅, B₇, B₉`. -/
def InFund5 (p : ℕ → ℝ) : Prop :=
  (0 ≤ p (bS 2) ∧ p (bS 2) ≤ Real.tan (Real.pi / 10)) ∧ (0 ≤ p (bS 3) ∧ p (bS 3) ≤ Real.tan (Real.pi / 7)) ∧
  (0 ≤ p (bS 4) ∧ p (bS 4) ≤ Real.tan (Real.pi / 9))

lemma flipC_one (ε : Bool) : flipC ε 1 = 1 := by cases ε <;> simp [flipC]

/-- **Normal form.** Congruent copies of `D, B₃, B₅, B₇, B₉` in a convex set `S ⊆ ℂ` give, after a common isometry,
a convex set of the same area containing the disk and the bodies placed by a placement in the fundamental domain. -/
theorem normal_form (h : Fin 5 → (ℂ ≃ᵢ ℂ)) {S : Set ℂ} (hS : Convex ℝ S)
    (h0 : h 0 '' diskC ⊆ S) (h1 : h 1 '' reuleauxC 3 ⊆ S) (h2 : h 2 '' reuleauxC 5 ⊆ S)
    (h3 : h 3 '' reuleauxC 7 ⊆ S) (h4 : h 4 '' reuleauxC 9 ⊆ S) :
    ∃ p, InFund5 p ∧ ∃ K : Set ℂ, Convex ℝ K ∧ volume K = volume S ∧ diskC ⊆ K ∧
      (∀ q ∈ reuleauxC 3, placeC p 1 q ∈ K) ∧ (∀ q ∈ reuleauxC 5, placeC p 2 q ∈ K) ∧
      (∀ q ∈ reuleauxC 7, placeC p 3 q ∈ K) ∧ (∀ q ∈ reuleauxC 9, placeC p 4 q ∈ K) := by
  obtain ⟨a0, b0, ha0, σ0, hh0⟩ := iso_flip (h 0)
  obtain ⟨a1, b1, ha1, σ1, hh1⟩ := iso_flip (h 1)
  obtain ⟨a2, b2, ha2, σ2, hh2⟩ := iso_flip (h 2)
  obtain ⟨a3, b3, ha3, σ3, hh3⟩ := iso_flip (h 3)
  obtain ⟨a4, b4, ha4, σ4, hh4⟩ := iso_flip (h 4)
  set c := (starRingEnd ℂ) a1 with hc
  have hcn : ‖c‖ = 1 := by rw [hc, Complex.norm_conj, ha1]
  have hca1 : c * a1 = 1 := by
    rw [hc, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha1]; simp
  have hpi := Real.pi_pos
  -- body 2 and the reflection flag
  obtain ⟨k2, ρ2, hρ20, hρ21, hv2⟩ := reduce_angle (n := 5) (by norm_num) (v := c * a2)
    (by rw [norm_mul, hcn, ha2, one_mul])
  have key : ∃ ε : Bool, ∃ k : ℕ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ Real.pi / 5 ∧
      flipC ε (c * a2) * exp (((2 * Real.pi * k / 5 : ℝ) : ℂ) * I) = exp ((ρ : ℂ) * I) := by
    by_cases hle : ρ2 ≤ Real.pi / 5
    · refine ⟨false, k2, ρ2, hρ20, hle, ?_⟩
      simp only [flipC]; exact_mod_cast hv2
    · push Not at hle
      obtain ⟨k', hk'⟩ := conj_reduce (n := 5) (by norm_num) hv2
      refine ⟨true, k', 2 * Real.pi / 5 - ρ2, ?_, ?_, ?_⟩
      · push_cast at hρ21; linarith
      · linarith
      · simp only [flipC, if_true]; push_cast at hk' ⊢; exact hk'
  obtain ⟨ε, k2', ρ2', hρ0, hρ1, hv2'⟩ := key
  -- bodies 3, 4
  obtain ⟨k3, ρ3, hρ30, hρ31, hv3⟩ := reduce_angle (n := 7) (by norm_num) (v := flipC ε (c * a3))
    (by rw [norm_flip, norm_mul, hcn, ha3, one_mul])
  obtain ⟨k4, ρ4, hρ40, hρ41, hv4⟩ := reduce_angle (n := 9) (by norm_num) (v := flipC ε (c * a4))
    (by rw [norm_flip, norm_mul, hcn, ha4, one_mul])
  -- the placement
  set t : ℕ → ℂ := fun i => if i = 1 then flipC ε (c * (b1 - b0)) else if i = 2 then flipC ε (c * (b2 - b0))
    else if i = 3 then flipC ε (c * (b3 - b0)) else flipC ε (c * (b4 - b0)) with ht
  set sv : ℕ → ℝ := fun i => if i = 2 then Real.tan (ρ2' / 2) else if i = 3 then Real.tan (ρ3 / 2)
    else Real.tan (ρ4 / 2) with hsv
  set p := mkPlace t sv with hp
  have hK : ∀ i (w : ℂ) (B : Set ℂ), h i '' B ⊆ S → w ∈ B → Phi ε c b0 (h i w) ∈ Phi ε c b0 '' S :=
    fun i w B hB hw => ⟨h i w, hB ⟨w, hw, rfl⟩, rfl⟩
  refine ⟨p, ?_, Phi ε c b0 '' S, Phi_convex ε c b0 hS, Phi_volume hcn ε b0 S, ?_, ?_, ?_, ?_, ?_⟩
  · -- fundamental domain
    have e2 : p (bS 2) = Real.tan (ρ2' / 2) := by rw [hp, mkPlace_s t sv (by norm_num)]; simp [hsv]
    have e3 : p (bS 3) = Real.tan (ρ3 / 2) := by rw [hp, mkPlace_s t sv (by norm_num)]; simp [hsv]
    have e4 : p (bS 4) = Real.tan (ρ4 / 2) := by rw [hp, mkPlace_s t sv (by norm_num)]; simp [hsv]
    refine ⟨?_, ?_, ?_⟩
    · rw [e2]
      have := tan_half_bounds (n := 10) (by norm_num) hρ0 (by push_cast; linarith)
      push_cast at this; exact this
    · rw [e3]
      have := tan_half_bounds (n := 7) (by norm_num) hρ30 hρ31.le
      push_cast at this; exact this
    · rw [e4]
      have := tan_half_bounds (n := 9) (by norm_num) hρ40 hρ41.le
      push_cast at this; exact this
  · -- the disk
    intro z hz
    set u := flipC ε (c * a0) with hu
    have hun : ‖u‖ = 1 := by rw [hu, norm_flip, norm_mul, hcn, ha0, one_mul]
    set w := flipC (xor ε σ0) ((starRingEnd ℂ) u * z) with hw
    have hwD : w ∈ diskC := by
      apply mem_diskC_of_norm
      rw [hw, norm_flip, norm_mul, Complex.norm_conj, hun, one_mul]
      simpa [diskC, Metric.mem_closedBall, dist_zero_right] using hz
    have := hK 0 w diskC h0 hwD
    rw [hh0, Phi_comp, ← hu, hw, flip_flip, sub_self, mul_zero] at this
    rw [show flipC ε 0 = 0 by cases ε <;> simp [flipC], add_zero, ← mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hun] at this
    simpa using this
  · -- body 1
    intro q hq
    have := hK 1 (flipC (xor ε σ1) q) (reuleauxC 3) h1 (mem_reuleauxC_flip (by norm_num) _ hq)
    rw [hh1, Phi_comp, hca1, flipC_one, one_mul, flip_flip] at this
    rw [hp, placeC_mk1]
    convert this using 2
    simp [ht]
  · -- body 2
    intro q hq
    obtain ⟨w, hwB, hweq⟩ := body_hits (n := 5) (by norm_num) (t := t 2) (xor ε σ2) (by exact_mod_cast hv2') hq
    have := hK 2 w (reuleauxC 5) h2 hwB
    rw [hh2, Phi_comp] at this
    rw [hp, placeC_mk (ρ := ρ2') (by norm_num) (by linarith) (by linarith) (by simp [hsv])]
    rw [← hweq]
    convert this using 2
    simp [ht]
  · -- body 3
    intro q hq
    obtain ⟨w, hwB, hweq⟩ := body_hits (n := 7) (by norm_num) (t := t 3) (xor ε σ3) (by exact_mod_cast hv3) hq
    have := hK 3 w (reuleauxC 7) h3 hwB
    rw [hh3, Phi_comp] at this
    have hρ31' : ρ3 < Real.pi := by push_cast at hρ31; linarith
    rw [hp, placeC_mk (ρ := ρ3) (by norm_num) (by linarith) hρ31' (by simp [hsv])]
    rw [← hweq]
    convert this using 2
    simp [ht]
  · -- body 4
    intro q hq
    obtain ⟨w, hwB, hweq⟩ := body_hits (n := 9) (by norm_num) (t := t 4) (xor ε σ4) (by exact_mod_cast hv4) hq
    have := hK 4 w (reuleauxC 9) h4 hwB
    rw [hh4, Phi_comp] at this
    have hρ41' : ρ4 < Real.pi := by push_cast at hρ41; linarith
    rw [hp, placeC_mk (ρ := ρ4) (by norm_num) (by linarith) hρ41' (by simp [hsv])]
    rw [← hweq]
    convert this using 2
    simp [ht]

end LebesgueCover.Cert
