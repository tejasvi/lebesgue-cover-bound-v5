import LebesgueCover.Checker

/-!
# Soundness of the reference leaf checker: algebraic part

Real counterparts of the checker's quantities, the bilinear expansion of a determinant of two affine
functions of `y`, and the lower bound of a quadratic on a box by absolute values.
-/

open Finset

namespace LebesgueCover.Cert

/-! ## Real counterparts and casts -/

def det2R (a b : ℝ × ℝ) : ℝ := a.1 * b.2 - a.2 * b.1
def dot2R (a b : ℝ × ℝ) : ℝ := a.1 * b.1 + a.2 * b.2
def castP (q : ℚ × ℚ) : ℝ × ℝ := ((q.1 : ℝ), (q.2 : ℝ))

@[simp] lemma castP_fst (q : ℚ × ℚ) : (castP q).1 = (q.1 : ℝ) := rfl
@[simp] lemma castP_snd (q : ℚ × ℚ) : (castP q).2 = (q.2 : ℝ) := rfl

lemma cast_det2 (a b : ℚ × ℚ) : ((det2 a b : ℚ) : ℝ) = det2R (castP a) (castP b) := by
  simp [det2, det2R]

lemma cast_dot2 (a b : ℚ × ℚ) : ((dot2 a b : ℚ) : ℝ) = dot2R (castP a) (castP b) := by
  simp [dot2, dot2R]

lemma cast_cuQ (s : ℚ) : ((cuQ s : ℚ) : ℝ) = cu (s : ℝ) := by
  simp [cuQ, cu]

lemma cast_suQ (s : ℚ) : ((suQ s : ℚ) : ℝ) = su (s : ℝ) := by
  simp [suQ, su]

/-! ## Affine functions of `y` and the bilinear expansion -/

/-- `P0 + Σ_{v<n} y_v L_v`. -/
noncomputable def lin (n : ℕ) (P0 : ℝ × ℝ) (L : ℕ → ℝ × ℝ) (y : ℕ → ℝ) : ℝ × ℝ :=
  (P0.1 + ∑ v ∈ range n, y v * (L v).1, P0.2 + ∑ v ∈ range n, y v * (L v).2)

/-- **Bilinear expansion** of `det(P0 + Ly, Q0 + My)`. -/
lemma det_lin (n : ℕ) (P0 Q0 : ℝ × ℝ) (L M : ℕ → ℝ × ℝ) (y : ℕ → ℝ) :
    det2R (lin n P0 L y) (lin n Q0 M y) =
      det2R P0 Q0 + ∑ a ∈ range n, (det2R P0 (M a) + det2R (L a) Q0) * y a +
        ∑ a ∈ range n, ∑ b ∈ range n, det2R (L a) (M b) * y a * y b := by
  unfold det2R lin
  simp only
  have e1 : (∑ v ∈ range n, y v * (L v).1) * (∑ v ∈ range n, y v * (M v).2) =
      ∑ a ∈ range n, ∑ b ∈ range n, (L a).1 * (M b).2 * y a * y b := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have e2 : (∑ v ∈ range n, y v * (L v).2) * (∑ v ∈ range n, y v * (M v).1) =
      ∑ a ∈ range n, ∑ b ∈ range n, (L a).2 * (M b).1 * y a * y b := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have e3 : ∑ a ∈ range n, ((P0.1 * (M a).2 - P0.2 * (M a).1) + ((L a).1 * Q0.2 - (L a).2 * Q0.1)) * y a =
      P0.1 * ∑ v ∈ range n, y v * (M v).2 - P0.2 * ∑ v ∈ range n, y v * (M v).1 +
        ((∑ v ∈ range n, y v * (L v).1) * Q0.2 - (∑ v ∈ range n, y v * (L v).2) * Q0.1) := by
    simp only [mul_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by ring
  have e4 : ∑ a ∈ range n, ∑ b ∈ range n, ((L a).1 * (M b).2 - (L a).2 * (M b).1) * y a * y b =
      ∑ a ∈ range n, ∑ b ∈ range n, (L a).1 * (M b).2 * y a * y b -
        ∑ a ∈ range n, ∑ b ∈ range n, (L a).2 * (M b).1 * y a * y b := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun a _ => by rw [← sum_sub_distrib]; exact sum_congr rfl fun b _ => by ring
  rw [e3, e4, ← e1, ← e2]
  ring

/-- **Quadratic on a box, absolute-value bound.** -/
lemma quad_abs_lower (n : ℕ) (c0 : ℝ) (g : ℕ → ℝ) (A : ℕ → ℕ → ℝ) (y y0 w : ℕ → ℝ)
    (hy : ∀ a ∈ range n, |y a - y0 a| ≤ w a) :
    c0 + ∑ a ∈ range n, g a * y0 a + ∑ a ∈ range n, ∑ b ∈ range n, A a b * y0 a * y0 b
      - ∑ a ∈ range n, |g a + ∑ b ∈ range n, (A a b + A b a) * y0 b| * w a
      - ∑ a ∈ range n, ∑ b ∈ range n, |A a b| * w a * w b ≤
    c0 + ∑ a ∈ range n, g a * y a + ∑ a ∈ range n, ∑ b ∈ range n, A a b * y a * y b := by
  set Δ : ℕ → ℝ := fun a => y a - y0 a with hΔ
  have hw0 : ∀ a ∈ range n, 0 ≤ w a := fun a ha => (abs_nonneg _).trans (hy a ha)
  -- exact expansion around y0
  have hexp : ∑ a ∈ range n, ∑ b ∈ range n, A a b * y a * y b =
      ∑ a ∈ range n, ∑ b ∈ range n, A a b * y0 a * y0 b +
        ∑ a ∈ range n, (∑ b ∈ range n, (A a b + A b a) * y0 b) * Δ a +
        ∑ a ∈ range n, ∑ b ∈ range n, A a b * Δ a * Δ b := by
    have key : ∀ a b, A a b * y a * y b = A a b * y0 a * y0 b + A a b * y0 b * Δ a + A a b * y0 a * Δ b +
        A a b * Δ a * Δ b := by intro a b; simp only [hΔ]; ring
    simp_rw [key, sum_add_distrib]
    have hswap : ∑ a ∈ range n, ∑ b ∈ range n, A a b * y0 a * Δ b =
        ∑ a ∈ range n, ∑ b ∈ range n, A b a * y0 b * Δ a := sum_comm
    rw [hswap]
    have hmerge : ∑ a ∈ range n, (∑ b ∈ range n, (A a b + A b a) * y0 b) * Δ a =
        ∑ a ∈ range n, ∑ b ∈ range n, A a b * y0 b * Δ a + ∑ a ∈ range n, ∑ b ∈ range n, A b a * y0 b * Δ a := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun a _ => by rw [sum_mul, ← sum_add_distrib]; exact sum_congr rfl fun b _ => by ring
    rw [hmerge]; ring
  have hgy : ∑ a ∈ range n, g a * y a = ∑ a ∈ range n, g a * y0 a + ∑ a ∈ range n, g a * Δ a := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun a _ => by simp only [hΔ]; ring
  -- linear part
  have hlin : -∑ a ∈ range n, |g a + ∑ b ∈ range n, (A a b + A b a) * y0 b| * w a ≤
      ∑ a ∈ range n, (g a + ∑ b ∈ range n, (A a b + A b a) * y0 b) * Δ a := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun a ha => ?_
    have h1 := hy a ha
    have h2 : -(|g a + ∑ b ∈ range n, (A a b + A b a) * y0 b| * |Δ a|) ≤
        (g a + ∑ b ∈ range n, (A a b + A b a) * y0 b) * Δ a := by rw [← abs_mul]; exact neg_abs_le _
    have h3 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (g a + ∑ b ∈ range n, (A a b + A b a) * y0 b))
    linarith
  -- quadratic part
  have hquad : -∑ a ∈ range n, ∑ b ∈ range n, |A a b| * w a * w b ≤
      ∑ a ∈ range n, ∑ b ∈ range n, A a b * Δ a * Δ b := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun a ha => ?_
    rw [← sum_neg_distrib]
    refine sum_le_sum fun b hb => ?_
    have h1 : |A a b * Δ a * Δ b| ≤ |A a b| * w a * w b := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hy a ha) (abs_nonneg _)) (hy b hb) (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) (hw0 a ha))
    exact neg_le_of_abs_le h1
  have hsplit : ∑ a ∈ range n, (g a + ∑ b ∈ range n, (A a b + A b a) * y0 b) * Δ a =
      ∑ a ∈ range n, g a * Δ a + ∑ a ∈ range n, (∑ b ∈ range n, (A a b + A b a) * y0 b) * Δ a := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun a _ => by ring
  rw [hgy, hexp]
  linarith

/-! ## Placements -/

def rot2R (u q : ℝ × ℝ) : ℝ × ℝ := (u.1 * q.1 - u.2 * q.2, u.2 * q.1 + u.1 * q.2)

/-- Rotation of body `i` at a placement `p` (box coordinates). -/
noncomputable def rotAt (p : ℕ → ℝ) (i : ℕ) : ℝ × ℝ := if i ≤ 1 then (1, 0) else (cu (p (bS i)), su (p (bS i)))

/-- Translation of body `i` at a placement `p`. -/
def transAt (p : ℕ → ℝ) (i : ℕ) : ℝ × ℝ := if i = 0 then (0, 0) else (p (bTx i), p (bTy i))

/-- Position of a witness at a placement. -/
noncomputable def witPos (p : ℕ → ℝ) (w : Wit) : ℝ × ℝ :=
  ((rot2R (rotAt p w.body) (castP w.pt)).1 + (transAt p w.body).1,
    (rot2R (rotAt p w.body) (castP w.pt)).2 + (transAt p w.body).2)

/-- The y-vector of a placement `p` relative to the leaf box `lo, hi`. -/
noncomputable def yAt (lo hi : ℕ → ℚ) (p : ℕ → ℝ) (v : ℕ) : ℝ :=
  match yKind v with
  | 0 => p (bTx (yBody v)) - ((bodyBox lo hi (yBody v)).tc.1 : ℝ)
  | 1 => p (bTy (yBody v)) - ((bodyBox lo hi (yBody v)).tc.2 : ℝ)
  | 2 => dot2R (castP (bodyBox lo hi (yBody v)).M) (cu (p (bS (yBody v))), su (p (bS (yBody v)))) - 1
  | _ => det2R (castP (bodyBox lo hi (yBody v)).M) (cu (p (bS (yBody v))), su (p (bS (yBody v))))

/-! ## Index facts -/

lemma yKind_yBody_tx {i : ℕ} (hi : 1 ≤ i) : yKind (yTx i) = 0 ∧ yBody (yTx i) = i := by
  unfold yKind yBody yTx
  rcases Nat.lt_or_ge i 2 with h | h
  · have : i = 1 := by omega
    subst this; simp
  · have h1 : i ≠ 1 := by omega
    simp only [h1, if_false]
    constructor
    · rw [if_neg (by omega)]; omega
    · rw [if_neg (by omega)]; omega

lemma yKind_yBody_ty {i : ℕ} (hi : 1 ≤ i) : yKind (yTy i) = 1 ∧ yBody (yTy i) = i := by
  unfold yKind yBody yTy
  rcases Nat.lt_or_ge i 2 with h | h
  · have : i = 1 := by omega
    subst this; simp
  · have h1 : i ≠ 1 := by omega
    simp only [h1, if_false]
    constructor
    · rw [if_neg (by omega)]; omega
    · rw [if_neg (by omega)]; omega

lemma yKind_yBody_C {i : ℕ} (hi : 2 ≤ i) : yKind (yC i) = 2 ∧ yBody (yC i) = i := by
  unfold yKind yBody yC
  constructor
  · rw [if_neg (by omega)]; omega
  · rw [if_neg (by omega)]; omega

lemma yKind_yBody_S {i : ℕ} (hi : 2 ≤ i) : yKind (yS i) = 3 ∧ yBody (yS i) = i := by
  unfold yKind yBody yS
  constructor
  · rw [if_neg (by omega)]; omega
  · rw [if_neg (by omega)]; omega

/-! ## Sums of if-chains -/

lemma sum_mul_ite_eq {n a : ℕ} (ha : a < n) (y : ℕ → ℝ) (c : ℝ) :
    ∑ v ∈ range n, y v * (if v = a then c else 0) = y a * c := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (mem_range.mpr ha) h

lemma sum_mul_ite2 {n a1 a2 : ℕ} (h1 : a1 < n) (h2 : a2 < n) (h12 : a1 ≠ a2) (y : ℕ → ℝ) (c1 c2 : ℝ) :
    ∑ v ∈ range n, y v * (if v = a1 then c1 else if v = a2 then c2 else 0) = y a1 * c1 + y a2 * c2 := by
  have e : ∀ v, (if v = a1 then c1 else if v = a2 then c2 else 0) =
      (if v = a1 then c1 else 0) + (if v = a2 then c2 else 0) := by
    intro v
    by_cases hv1 : v = a1
    · subst hv1; simp [h12]
    · by_cases hv2 : v = a2
      · subst hv2; simp [hv1, Ne.symm h12]
      · simp [hv1, hv2]
  simp_rw [e, mul_add, sum_add_distrib, sum_mul_ite_eq h1, sum_mul_ite_eq h2]

lemma sum_mul_ite4 {n a1 a2 a3 a4 : ℕ} (h1 : a1 < n) (h2 : a2 < n) (h3 : a3 < n) (h4 : a4 < n)
    (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h14 : a1 ≠ a4) (h23 : a2 ≠ a3) (h24 : a2 ≠ a4) (h34 : a3 ≠ a4)
    (y : ℕ → ℝ) (c1 c2 c3 c4 : ℝ) :
    ∑ v ∈ range n, y v * (if v = a1 then c1 else if v = a2 then c2 else if v = a3 then c3 else
      if v = a4 then c4 else 0) = y a1 * c1 + y a2 * c2 + y a3 * c3 + y a4 * c4 := by
  have e : ∀ v, (if v = a1 then c1 else if v = a2 then c2 else if v = a3 then c3 else if v = a4 then c4 else 0) =
      (if v = a1 then c1 else 0) + (if v = a2 then c2 else 0) + (if v = a3 then c3 else 0) +
        (if v = a4 then c4 else 0) := by
    intro v
    by_cases hv1 : v = a1
    · subst hv1; simp [h12, h13, h14]
    · by_cases hv2 : v = a2
      · subst hv2; simp [hv1, h23, h24, Ne.symm h12]
      · by_cases hv3 : v = a3
        · subst hv3; simp [hv1, hv2, h34, Ne.symm h13, Ne.symm h23]
        · by_cases hv4 : v = a4
          · subst hv4; simp [hv1, hv2, hv3, Ne.symm h14, Ne.symm h24, Ne.symm h34]
          · simp [hv1, hv2, hv3, hv4]
  simp_rw [e, mul_add, sum_add_distrib, sum_mul_ite_eq h1, sum_mul_ite_eq h2, sum_mul_ite_eq h3,
    sum_mul_ite_eq h4]

/-! ## Witness positions are affine in `y` -/

lemma bodyBox_M_cast (lo hi : ℕ → ℚ) {i : ℕ} (hi2 : 2 ≤ i) :
    castP (bodyBox lo hi i).M = (cu (((lo (bS i) + hi (bS i)) / 2 : ℚ) : ℝ), su (((lo (bS i) + hi (bS i)) / 2 : ℚ) : ℝ)) := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  simp only [bodyBox, h0, h1, if_false, uQ, castP, cast_cuQ, cast_suQ]

lemma bodyBox_tc (lo hi : ℕ → ℚ) {i : ℕ} (hi1 : 1 ≤ i) :
    (bodyBox lo hi i).tc = ((lo (bTx i) + hi (bTx i)) / 2, (lo (bTy i) + hi (bTy i)) / 2) := by
  have h0 : i ≠ 0 := by omega
  by_cases h1 : i = 1
  · subst h1; simp [bodyBox]
  · simp [bodyBox, h0, h1]

lemma bodyBox_M_one (lo hi : ℕ → ℚ) : (bodyBox lo hi 1).M = (1, 0) := by simp [bodyBox]
lemma bodyBox_M_zero (lo hi : ℕ → ℚ) : (bodyBox lo hi 0).M = (1, 0) := by simp [bodyBox]

/-- **Witness positions are affine in the y-vector.** -/
lemma witPos_eq_lin (lo hi : ℕ → ℚ) (p : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k) (w : Wit) (hw : w.body ≤ k) :
    witPos p w = lin (4 * k - 2) (castP (witX0 (bodyBox lo hi) w))
      (fun v => castP (witL (bodyBox lo hi) w v)) (yAt lo hi p) := by
  obtain ⟨i, q⟩ := w
  simp only at hw
  rcases Nat.lt_or_ge i 2 with hb | hb
  · rcases Nat.lt_or_ge i 1 with hb0 | hb1
    · -- the disk
      have : i = 0 := by omega
      subst this
      simp [witPos, lin, witX0, witL, rotAt, transAt, rot2R, castP]
    · -- body 1 (translated, not rotated)
      have : i = 1 := by omega
      subst this
      have hsum1 : ∑ v ∈ range (4 * k - 2), yAt lo hi p v *
          ((witL (bodyBox lo hi) ⟨1, q⟩ v).1 : ℝ) = yAt lo hi p 0 := by
        have e : ∀ v, ((witL (bodyBox lo hi) ⟨1, q⟩ v).1 : ℝ) = if v = 0 then 1 else if v = 1 then 0 else 0 := by
          intro v; simp only [witL, yTx, yTy]; split_ifs <;> simp_all
        simp_rw [e]
        rw [sum_mul_ite2 (by omega) (by omega) (by omega)]; ring
      have hsum2 : ∑ v ∈ range (4 * k - 2), yAt lo hi p v *
          ((witL (bodyBox lo hi) ⟨1, q⟩ v).2 : ℝ) = yAt lo hi p 1 := by
        have e : ∀ v, ((witL (bodyBox lo hi) ⟨1, q⟩ v).2 : ℝ) = if v = 0 then 0 else if v = 1 then 1 else 0 := by
          intro v; simp only [witL, yTx, yTy]; split_ifs <;> simp_all
        simp_rw [e]
        rw [sum_mul_ite2 (by omega) (by omega) (by omega)]; ring
      have y0 : yAt lo hi p 0 = p (bTx 1) - ((bodyBox lo hi 1).tc.1 : ℝ) := by
        simp [yAt, yKind, yBody]
      have y1 : yAt lo hi p 1 = p (bTy 1) - ((bodyBox lo hi 1).tc.2 : ℝ) := by
        simp [yAt, yKind, yBody]
      simp only [lin, castP_fst, castP_snd, hsum1, hsum2, y0, y1]
      simp only [witPos, witX0, rotAt, transAt, rot2R, rot2, castP, bodyBox_M_one]
      simp
  · -- body i ≥ 2
    have hi0 : i ≠ 0 := by omega
    have hi1 : i ≠ 1 := by omega
    set bb := bodyBox lo hi with hbb
    set M := (bb i).M with hM
    set a := rot2 M q with ha
    have hTx : yTx i = 4 * i - 6 := by simp [yTx, hi1]
    have hTy : yTy i = 4 * i - 5 := by simp [yTy, hi1]
    have hlt : ∀ v ∈ [4 * i - 6, 4 * i - 5, 4 * i - 4, 4 * i - 3], v < 4 * k - 2 := by
      intro v hv; simp at hv; omega
    have e1 : ∀ v, ((witL bb ⟨i, q⟩ v).1 : ℝ) = if v = 4 * i - 6 then 1 else if v = 4 * i - 5 then 0 else
        if v = 4 * i - 4 then (a.1 : ℝ) else if v = 4 * i - 3 then -(a.2 : ℝ) else 0 := by
      intro v
      simp only [witL, hi0, if_false, hTx, hTy, yC, yS, hb, true_and, J2, ← ha, ← hM]
      split_ifs <;> simp
    have e2 : ∀ v, ((witL bb ⟨i, q⟩ v).2 : ℝ) = if v = 4 * i - 6 then 0 else if v = 4 * i - 5 then 1 else
        if v = 4 * i - 4 then (a.2 : ℝ) else if v = 4 * i - 3 then (a.1 : ℝ) else 0 := by
      intro v
      simp only [witL, hi0, if_false, hTx, hTy, yC, yS, hb, true_and, J2, ← ha, ← hM]
      split_ifs <;> simp
    have hs1 := sum_mul_ite4 (n := 4 * k - 2) (a1 := 4 * i - 6) (a2 := 4 * i - 5) (a3 := 4 * i - 4) (a4 := 4 * i - 3)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (yAt lo hi p) 1 0 (a.1 : ℝ) (-(a.2 : ℝ))
    have hs2 := sum_mul_ite4 (n := 4 * k - 2) (a1 := 4 * i - 6) (a2 := 4 * i - 5) (a3 := 4 * i - 4) (a4 := 4 * i - 3)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (yAt lo hi p) 0 1 (a.2 : ℝ) (a.1 : ℝ)
    have yTxv : yAt lo hi p (4 * i - 6) = p (bTx i) - ((bb i).tc.1 : ℝ) := by
      have := yKind_yBody_tx (by omega : 1 ≤ i); rw [hTx] at this
      simp only [yAt, this.1, this.2, hbb]
    have yTyv : yAt lo hi p (4 * i - 5) = p (bTy i) - ((bb i).tc.2 : ℝ) := by
      have := yKind_yBody_ty (by omega : 1 ≤ i); rw [hTy] at this
      simp only [yAt, this.1, this.2, hbb]
    have yCv : yAt lo hi p (4 * i - 4) = dot2R (castP M) (cu (p (bS i)), su (p (bS i))) - 1 := by
      have := yKind_yBody_C hb; simp only [yC] at this
      simp only [yAt, this.1, this.2, hM, hbb]
    have ySv : yAt lo hi p (4 * i - 3) = det2R (castP M) (cu (p (bS i)), su (p (bS i))) := by
      have := yKind_yBody_S hb; simp only [yS] at this
      simp only [yAt, this.1, this.2, hM, hbb]
    have hMc := bodyBox_M_cast lo hi hb
    rw [← hbb, ← hM] at hMc
    simp only [lin, castP_fst, castP_snd]
    simp_rw [e1, e2]
    rw [hs1, hs2, yTxv, yTyv, yCv, ySv]
    -- the rotation identity u(s) = u(m) · (cos δ, sin δ)
    set m : ℝ := (((lo (bS i) + hi (bS i)) / 2 : ℚ) : ℝ)
    set sv := p (bS i)
    have hcomp := u_compose m sv
    have hcm := cu_sq_add_su_sq m
    have hMm : castP M = (cu m, su m) := hMc
    have hcast_a : ((a.1 : ℚ) : ℝ) = cu m * (q.1 : ℝ) - su m * (q.2 : ℝ) ∧
        ((a.2 : ℚ) : ℝ) = su m * (q.1 : ℝ) + cu m * (q.2 : ℝ) := by
      have h1 : ((M.1 : ℚ) : ℝ) = cu m := congrArg Prod.fst hMm
      have h2 : ((M.2 : ℚ) : ℝ) = su m := congrArg Prod.snd hMm
      simp only [ha, rot2]; push_cast; rw [h1, h2]; exact ⟨rfl, rfl⟩
    have hA1 : ((rot2 (bodyBox lo hi i).M q).1 : ℝ) = cu m * (q.1 : ℝ) - su m * (q.2 : ℝ) := by
      rw [← hbb, ← hM, ← ha]; exact hcast_a.1
    have hA2 : ((rot2 (bodyBox lo hi i).M q).2 : ℝ) = su m * (q.1 : ℝ) + cu m * (q.2 : ℝ) := by
      rw [← hbb, ← hM, ← ha]; exact hcast_a.2
    simp only [witPos, rotAt, transAt, hi0, if_false, show ¬ i ≤ 1 by omega, rot2R, castP_fst, castP_snd,
      witX0, ← ha, ← hM, hbb, dot2R, det2R, hMm]
    rw [hcast_a.1, hcast_a.2]
    push_cast
    ext
    · simp only
      linear_combination (-(cu sv * (q.1 : ℝ) - su sv * (q.2 : ℝ))) * hcm + (-1 : ℝ) * hA1
    · simp only
      linear_combination (-(su sv * (q.1 : ℝ) + cu sv * (q.2 : ℝ))) * hcm + (-1 : ℝ) * hA2

/-! ## The y-vector lies in the y-box -/

lemma v_cases {v k : ℕ} (hv : v < 4 * k - 2) :
    v = 0 ∨ v = 1 ∨ ∃ i, 2 ≤ i ∧ i ≤ k ∧ (v = 4 * i - 6 ∨ v = 4 * i - 5 ∨ v = 4 * i - 4 ∨ v = 4 * i - 3) := by
  rcases Nat.lt_or_ge v 2 with h | h
  · omega
  · exact Or.inr (Or.inr ⟨(v + 6) / 4, by omega, by omega, by omega⟩)

/-- The translation part of the box. -/
lemma t_bound {l h : ℚ} {x : ℝ} (h1 : (l : ℝ) ≤ x) (h2 : x ≤ h) :
    |x - (((l + h) / 2 : ℚ) : ℝ)| ≤ (((h - l) / 2 : ℚ) : ℝ) := by
  push_cast
  rw [abs_le]; constructor <;> linarith

lemma bodyBox_ht (lo hi : ℕ → ℚ) {i : ℕ} (hi1 : 1 ≤ i) :
    (bodyBox lo hi i).ht = ((hi (bTx i) - lo (bTx i)) / 2, (hi (bTy i) - lo (bTy i)) / 2) := by
  have h0 : i ≠ 0 := by omega
  by_cases h1 : i = 1
  · subst h1; simp [bodyBox]
  · simp [bodyBox, h0, h1]

lemma yTx_two {i : ℕ} (h : 2 ≤ i) : yTx i = 4 * i - 6 := by simp [yTx, show i ≠ 1 by omega]
lemma yTy_two {i : ℕ} (h : 2 ≤ i) : yTy i = 4 * i - 5 := by simp [yTy, show i ≠ 1 by omega]

/-- Bounds for the translation coordinates of body `i ≥ 1`. -/
lemma yAt_t_bound (lo hi : ℕ → ℚ) (p : ℕ → ℝ) {i : ℕ} (hi1 : 1 ≤ i)
    (hx : (lo (bTx i) : ℝ) ≤ p (bTx i) ∧ p (bTx i) ≤ hi (bTx i))
    (hy : (lo (bTy i) : ℝ) ≤ p (bTy i) ∧ p (bTy i) ≤ hi (bTy i)) :
    |yAt lo hi p (yTx i) - (yCentre (bodyBox lo hi) (yTx i) : ℝ)| ≤ (yHalf (bodyBox lo hi) (yTx i) : ℝ) ∧
    |yAt lo hi p (yTy i) - (yCentre (bodyBox lo hi) (yTy i) : ℝ)| ≤ (yHalf (bodyBox lo hi) (yTy i) : ℝ) := by
  obtain ⟨kx, bx⟩ := yKind_yBody_tx hi1
  obtain ⟨ky, by'⟩ := yKind_yBody_ty hi1
  simp only [yAt, yCentre, yHalf, kx, bx, ky, by', bodyBox_tc lo hi hi1, bodyBox_ht lo hi hi1]
  simp only [show (0 : ℕ) ≠ 2 from by decide, show (1 : ℕ) ≠ 2 from by decide, if_false, Rat.cast_zero, sub_zero]
  exact ⟨t_bound hx.1 hx.2, t_bound hy.1 hy.2⟩

/-- Bounds for the rotation coordinates of body `i ≥ 2`. -/
lemma yAt_rot_bound (lo hi : ℕ → ℚ) (p : ℕ → ℝ) {i : ℕ} (hi2 : 2 ≤ i) (hsok : (bodyBox lo hi i).sOK = true)
    (hs : (lo (bS i) : ℝ) ≤ p (bS i) ∧ p (bS i) ≤ hi (bS i)) :
    |yAt lo hi p (yC i) - (yCentre (bodyBox lo hi) (yC i) : ℝ)| ≤ (yHalf (bodyBox lo hi) (yC i) : ℝ) ∧
    |yAt lo hi p (yS i) - (yCentre (bodyBox lo hi) (yS i) : ℝ)| ≤ (yHalf (bodyBox lo hi) (yS i) : ℝ) := by
  have hi0 : i ≠ 0 := by omega
  have hi1 : i ≠ 1 := by omega
  simp only [bodyBox, hi0, hi1, if_false, decide_eq_true_eq] at hsok
  obtain ⟨hl0, hlh, hh1⟩ := hsok
  have hlh' : (lo (bS i) : ℝ) ≤ hi (bS i) := by exact_mod_cast hlh
  have hrr := rot_range (lo := (lo (bS i) : ℝ)) (m := (((lo (bS i) + hi (bS i)) / 2 : ℚ) : ℝ))
    (hi := (hi (bS i) : ℝ)) (s := p (bS i))
    (by exact_mod_cast hl0) (by push_cast; linarith) (by push_cast; linarith) (by exact_mod_cast hh1) hs
  obtain ⟨kC, bC⟩ := yKind_yBody_C hi2
  obtain ⟨kS, bS'⟩ := yKind_yBody_S hi2
  obtain ⟨hA, hB, hC⟩ := hrr
  constructor
  · simp only [yAt, yCentre, yHalf, kC, bC, if_true, bodyBox, hi0, hi1, if_false, uQ, dot2R, castP, dot2]
    push_cast
    simp only [cast_cuQ, cast_suQ]
    rw [abs_le]; constructor <;> linarith
  · simp only [yAt, yCentre, yHalf, kS, bS', show (3 : ℕ) ≠ 2 from by decide, if_false, bodyBox, hi0, hi1,
      uQ, det2R, castP, det2, Rat.cast_zero, sub_zero]
    push_cast
    simp only [cast_cuQ, cast_suQ]
    exact hC

/-- **The y-vector of a placement in the box lies in the y-box.** -/
lemma yAt_mem_box (lo hi : ℕ → ℚ) (p : ℕ → ℝ) {k : ℕ}
    (hs : ∀ i, 2 ≤ i → i ≤ k → (bodyBox lo hi i).sOK = true)
    (hp : ∀ a, a < 3 * k - 1 → (lo a : ℝ) ≤ p a ∧ p a ≤ hi a) :
    ∀ v ∈ range (4 * k - 2), |yAt lo hi p v - (yCentre (bodyBox lo hi) v : ℝ)| ≤ (yHalf (bodyBox lo hi) v : ℝ) := by
  intro v hv
  rw [mem_range] at hv
  rcases v_cases hv with rfl | rfl | ⟨i, hi2, hik, h⟩
  · have := yAt_t_bound lo hi p (le_refl 1) (hp 0 (by omega)) (hp 1 (by omega))
    simpa [yTx] using this.1
  · have := yAt_t_bound lo hi p (le_refl 1) (hp 0 (by omega)) (hp 1 (by omega))
    simpa [yTy] using this.2
  · have ht := yAt_t_bound lo hi p (by omega : 1 ≤ i) (hp (bTx i) (by unfold bTx; split_ifs <;> omega))
      (hp (bTy i) (by unfold bTy; split_ifs <;> omega))
    have hr := yAt_rot_bound lo hi p hi2 (hs i hi2 hik) (hp (bS i) (by unfold bS; omega))
    rw [yTx_two hi2] at ht; rw [yTy_two hi2] at ht
    simp only [yC, yS] at hr
    rcases h with rfl | rfl | rfl | rfl
    · exact ht.1
    · exact ht.2
    · exact hr.1
    · exact hr.2

/-! ## Fan rows: positive determinants on the box -/

/-- `a − z` in `ℝ²`. -/
def subR (a z : ℝ × ℝ) : ℝ × ℝ := (a.1 - z.1, a.2 - z.2)

lemma castP_sub (a z : ℚ × ℚ) : castP (a.1 - z.1, a.2 - z.2) = subR (castP a) (castP z) := by
  simp [castP, subR]

lemma lin_sub (n : ℕ) (P0 z : ℝ × ℝ) (L : ℕ → ℝ × ℝ) (y : ℕ → ℝ) :
    subR (lin n P0 L y) z = lin n (subR P0 z) L y := by
  simp only [subR, lin]; ext <;> simp <;> ring

lemma cast_quadLowerAbs (nv : ℕ) (c0 : ℚ) (g : ℕ → ℚ) (A : ℕ → ℕ → ℚ) (y0 w : ℕ → ℚ) :
    ((quadLowerAbs nv c0 g A y0 w : ℚ) : ℝ) =
      (c0 : ℝ) + ∑ a ∈ range nv, (g a : ℝ) * (y0 a : ℝ) + ∑ a ∈ range nv, ∑ b ∈ range nv, (A a b : ℝ) * y0 a * y0 b
        - ∑ a ∈ range nv, |(g a : ℝ) + ∑ b ∈ range nv, ((A a b : ℝ) + (A b a : ℝ)) * (y0 b : ℝ)| * (w a : ℝ)
        - ∑ a ∈ range nv, ∑ b ∈ range nv, |(A a b : ℝ)| * (w a : ℝ) * (w b : ℝ) := by
  simp [quadLowerAbs]

/-- **A positive fan row gives a positive determinant on the whole y-box.** -/
lemma fanRow_sound_y (lo hi : ℕ → ℚ) {k : ℕ} (z : ℚ × ℚ) (w w' : Wit) (y : ℕ → ℝ)
    (hbox : ∀ v ∈ range (4 * k - 2), |y v - (yCentre (bodyBox lo hi) v : ℝ)| ≤ (yHalf (bodyBox lo hi) v : ℝ))
    (h : 0 < fanRow (4 * k - 2) (bodyBox lo hi) z w w') :
    0 < det2R
      (lin (4 * k - 2) (subR (castP (witX0 (bodyBox lo hi) w)) (castP z)) (fun v => castP (witL (bodyBox lo hi) w v)) y)
      (lin (4 * k - 2) (subR (castP (witX0 (bodyBox lo hi) w')) (castP z)) (fun v => castP (witL (bodyBox lo hi) w' v))
        y) := by
  rw [det_lin]
  have hq := quad_abs_lower (4 * k - 2)
    (det2R (subR (castP (witX0 (bodyBox lo hi) w)) (castP z)) (subR (castP (witX0 (bodyBox lo hi) w')) (castP z)))
    (fun a => det2R (subR (castP (witX0 (bodyBox lo hi) w)) (castP z)) (castP (witL (bodyBox lo hi) w' a)) +
      det2R (castP (witL (bodyBox lo hi) w a)) (subR (castP (witX0 (bodyBox lo hi) w')) (castP z)))
    (fun a b => det2R (castP (witL (bodyBox lo hi) w a)) (castP (witL (bodyBox lo hi) w' b)))
    y (fun a => (yCentre (bodyBox lo hi) a : ℝ)) (fun a => (yHalf (bodyBox lo hi) a : ℝ)) hbox
  refine lt_of_lt_of_le ?_ hq
  have hcast : ((fanRow (4 * k - 2) (bodyBox lo hi) z w w' : ℚ) : ℝ) =
      det2R (subR (castP (witX0 (bodyBox lo hi) w)) (castP z)) (subR (castP (witX0 (bodyBox lo hi) w')) (castP z))
        + ∑ a ∈ range (4 * k - 2),
            (det2R (subR (castP (witX0 (bodyBox lo hi) w)) (castP z)) (castP (witL (bodyBox lo hi) w' a)) +
              det2R (castP (witL (bodyBox lo hi) w a)) (subR (castP (witX0 (bodyBox lo hi) w')) (castP z))) *
              (yCentre (bodyBox lo hi) a : ℝ)
        + ∑ a ∈ range (4 * k - 2), ∑ b ∈ range (4 * k - 2),
            det2R (castP (witL (bodyBox lo hi) w a)) (castP (witL (bodyBox lo hi) w' b)) *
              (yCentre (bodyBox lo hi) a : ℝ) * (yCentre (bodyBox lo hi) b : ℝ)
        - ∑ a ∈ range (4 * k - 2),
            |det2R (subR (castP (witX0 (bodyBox lo hi) w)) (castP z)) (castP (witL (bodyBox lo hi) w' a)) +
              det2R (castP (witL (bodyBox lo hi) w a)) (subR (castP (witX0 (bodyBox lo hi) w')) (castP z)) +
              ∑ b ∈ range (4 * k - 2),
                (det2R (castP (witL (bodyBox lo hi) w a)) (castP (witL (bodyBox lo hi) w' b)) +
                  det2R (castP (witL (bodyBox lo hi) w b)) (castP (witL (bodyBox lo hi) w' a))) *
                  (yCentre (bodyBox lo hi) b : ℝ)| * (yHalf (bodyBox lo hi) a : ℝ)
        - ∑ a ∈ range (4 * k - 2), ∑ b ∈ range (4 * k - 2),
            |det2R (castP (witL (bodyBox lo hi) w a)) (castP (witL (bodyBox lo hi) w' b))| *
              (yHalf (bodyBox lo hi) a : ℝ) * (yHalf (bodyBox lo hi) b : ℝ) := by
    simp only [fanRow, cast_quadLowerAbs, pairC0, pairG, pairA, Rat.cast_add, cast_det2, castP_sub]
  rw [← hcast]
  exact_mod_cast h

/-- **A positive fan row gives a positive determinant at every placement of the box.** -/
lemma fanRow_sound (lo hi : ℕ → ℚ) (p : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k)
    (hs : ∀ i, 2 ≤ i → i ≤ k → (bodyBox lo hi i).sOK = true)
    (hp : ∀ a, a < 3 * k - 1 → (lo a : ℝ) ≤ p a ∧ p a ≤ hi a)
    (z : ℚ × ℚ) (w w' : Wit) (hw : w.body ≤ k) (hw' : w'.body ≤ k)
    (h : 0 < fanRow (4 * k - 2) (bodyBox lo hi) z w w') :
    0 < det2R (subR (witPos p w) (castP z)) (subR (witPos p w') (castP z)) := by
  rw [witPos_eq_lin lo hi p hk w hw, witPos_eq_lin lo hi p hk w' hw', lin_sub, lin_sub]
  exact fanRow_sound_y lo hi z w w' (yAt lo hi p) (yAt_mem_box lo hi p hs hp) h

/-! ## The fan area as a quadratic in `y` -/

/-- Real fan area `(1/2) Σ det(x_j, x_{j+1})` of a witness list at a placement. -/
noncomputable def fanAreaR (p : ℕ → ℝ) (W : List Wit) : ℝ :=
  ((cycPairs W).map fun pr => det2R (witPos p pr.1) (witPos p pr.2) / 2).sum

lemma list_sum_finset_sum {α : Type} (l : List α) (s : Finset ℕ) (f : α → ℕ → ℝ) :
    (l.map fun x => ∑ a ∈ s, f x a).sum = ∑ a ∈ s, (l.map fun x => f x a).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, sum_add_distrib]

lemma list_sum_add {α : Type} (l : List α) (f g : α → ℝ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]; ring

lemma list_sum_mul_const {α : Type} (l : List α) (f : α → ℝ) (c : ℝ) :
    (l.map fun x => f x * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]; ring

lemma list_sum_div_const {α : Type} (l : List α) (f : α → ℝ) (c : ℝ) :
    (l.map fun x => f x / c).sum = (l.map f).sum / c := by
  simp_rw [div_eq_mul_inv]; exact list_sum_mul_const l f c⁻¹

lemma cast_list_sum {α : Type} (l : List α) (f : α → ℚ) :
    (((l.map f).sum : ℚ) : ℝ) = (l.map fun x => (f x : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

/-- The β-terms that the checker adds (zero at real placements). -/
noncomputable def betaSum (nv : ℕ) (β : ℕ → ℚ) (y : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range nv, (β (yBody a) : ℝ) *
    ((if yKind a = 2 then 2 * y a else 0) + (if yKind a = 2 ∨ yKind a = 3 then y a ^ 2 else 0))

lemma mem_cycPairs_body {W : List Wit} {k : ℕ} (hW : ∀ w ∈ W, w.body ≤ k) :
    ∀ pr ∈ cycPairs W, pr.1.body ≤ k ∧ pr.2.body ≤ k := by
  intro pr hpr
  cases W with
  | nil => simp [cycPairs] at hpr
  | cons a t =>
    simp only [cycPairs] at hpr
    have h1 := List.of_mem_zip hpr
    refine ⟨hW _ h1.1, hW _ ?_⟩
    rcases List.mem_append.mp h1.2 with h | h
    · exact List.mem_cons_of_mem _ h
    · simp at h; rw [h]; exact List.mem_cons_self

/-- **The checker's quadratic evaluates to the fan area plus the β-terms.** -/
lemma fanQuad_eval (lo hi : ℕ → ℚ) (p : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k) (W : List Wit)
    (hW : ∀ w ∈ W, w.body ≤ k) (β : ℕ → ℚ) :
    ((fanQuad (bodyBox lo hi) W β).F0 : ℝ) +
        ∑ a ∈ range (4 * k - 2), ((fanQuad (bodyBox lo hi) W β).g a : ℝ) * yAt lo hi p a +
        (∑ a ∈ range (4 * k - 2), ∑ b ∈ range (4 * k - 2),
          ((fanQuad (bodyBox lo hi) W β).H a b : ℝ) * yAt lo hi p a * yAt lo hi p b) / 2 =
      fanAreaR p W + betaSum (4 * k - 2) β (yAt lo hi p) := by
  set n := 4 * k - 2
  set y := yAt lo hi p
  set bb := bodyBox lo hi
  set prs := cycPairs W
  have hpb := mem_cycPairs_body hW
  -- per-pair expansion
  have hpair : ∀ pr ∈ prs, det2R (witPos p pr.1) (witPos p pr.2) / 2 =
      (pairC0 (witX0 bb pr.1) (witX0 bb pr.2) : ℝ) / 2 +
        ∑ a ∈ range n, ((pairG (witX0 bb pr.1) (witX0 bb pr.2) (witL bb pr.1) (witL bb pr.2) a : ℝ) / 2) * y a +
        ∑ a ∈ range n, ∑ b ∈ range n, ((pairA (witL bb pr.1) (witL bb pr.2) a b : ℝ) / 2) * y a * y b := by
    intro pr hpr
    obtain ⟨h1, h2⟩ := hpb pr hpr
    rw [witPos_eq_lin lo hi p hk pr.1 h1, witPos_eq_lin lo hi p hk pr.2 h2, det_lin]
    simp only [pairC0, pairG, pairA, Rat.cast_add, cast_det2]
    simp only [add_div, sum_div]
    congr 1
    · congr 1
      exact sum_congr rfl fun a _ => by ring
    · exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have hfan : fanAreaR p W =
      (prs.map fun pr => (pairC0 (witX0 bb pr.1) (witX0 bb pr.2) : ℝ) / 2).sum +
        ∑ a ∈ range n, (prs.map fun pr =>
          ((pairG (witX0 bb pr.1) (witX0 bb pr.2) (witL bb pr.1) (witL bb pr.2) a : ℝ) / 2)).sum * y a +
        ∑ a ∈ range n, ∑ b ∈ range n, (prs.map fun pr =>
          ((pairA (witL bb pr.1) (witL bb pr.2) a b : ℝ) / 2)).sum * y a * y b := by
    unfold fanAreaR
    rw [List.map_congr_left hpair, list_sum_add, list_sum_add, list_sum_finset_sum, list_sum_finset_sum]
    congr 1
    · congr 1
      exact sum_congr rfl fun a _ => list_sum_mul_const _ _ _
    · exact sum_congr rfl fun a _ => by
        rw [list_sum_finset_sum]
        exact sum_congr rfl fun b _ => by
          rw [← list_sum_mul_const, ← list_sum_mul_const]
  -- the checker's coefficients
  have hF0 : ((fanQuad bb W β).F0 : ℝ) = (prs.map fun pr => (pairC0 (witX0 bb pr.1) (witX0 bb pr.2) : ℝ) / 2).sum := by
    simp only [fanQuad, cast_list_sum, Rat.cast_div, Rat.cast_ofNat]
    rfl
  have hg : ∀ a, ((fanQuad bb W β).g a : ℝ) =
      (prs.map fun pr => ((pairG (witX0 bb pr.1) (witX0 bb pr.2) (witL bb pr.1) (witL bb pr.2) a : ℝ) / 2)).sum +
        (if yKind a = 2 then 2 * (β (yBody a) : ℝ) else 0) := by
    intro a
    simp only [fanQuad, Rat.cast_add, cast_list_sum, Rat.cast_div, Rat.cast_ofNat]
    split_ifs <;> simp [prs]
  have hH : ∀ a b, ((fanQuad bb W β).H a b : ℝ) =
      (prs.map fun pr => (((pairA (witL bb pr.1) (witL bb pr.2) a b : ℝ) +
        (pairA (witL bb pr.1) (witL bb pr.2) b a : ℝ)) / 2)).sum +
        (if a = b ∧ (yKind a = 2 ∨ yKind a = 3) then 2 * (β (yBody a) : ℝ) else 0) := by
    intro a b
    simp only [fanQuad, Rat.cast_add, cast_list_sum, Rat.cast_div, Rat.cast_ofNat]
    split_ifs <;> simp [prs]
  rw [hfan, hF0]
  simp_rw [hg, hH]
  -- split the β parts
  have hsplit_g : ∑ a ∈ range n,
      ((prs.map fun pr => ((pairG (witX0 bb pr.1) (witX0 bb pr.2) (witL bb pr.1) (witL bb pr.2) a : ℝ) / 2)).sum +
        (if yKind a = 2 then 2 * (β (yBody a) : ℝ) else 0)) * y a =
      ∑ a ∈ range n, (prs.map fun pr =>
        ((pairG (witX0 bb pr.1) (witX0 bb pr.2) (witL bb pr.1) (witL bb pr.2) a : ℝ) / 2)).sum * y a +
      ∑ a ∈ range n, (β (yBody a) : ℝ) * (if yKind a = 2 then 2 * y a else 0) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun a _ => by split_ifs <;> ring
  have hsplit_H : ∑ a ∈ range n, ∑ b ∈ range n,
      ((prs.map fun pr => (((pairA (witL bb pr.1) (witL bb pr.2) a b : ℝ) +
        (pairA (witL bb pr.1) (witL bb pr.2) b a : ℝ)) / 2)).sum +
        (if a = b ∧ (yKind a = 2 ∨ yKind a = 3) then 2 * (β (yBody a) : ℝ) else 0)) * y a * y b =
      2 * ∑ a ∈ range n, ∑ b ∈ range n, (prs.map fun pr =>
          ((pairA (witL bb pr.1) (witL bb pr.2) a b : ℝ) / 2)).sum * y a * y b +
      2 * ∑ a ∈ range n, (β (yBody a) : ℝ) * (if yKind a = 2 ∨ yKind a = 3 then y a ^ 2 else 0) := by
    have hsym : ∑ a ∈ range n, ∑ b ∈ range n, (prs.map fun pr =>
          ((pairA (witL bb pr.1) (witL bb pr.2) b a : ℝ) / 2)).sum * y a * y b =
        ∑ a ∈ range n, ∑ b ∈ range n, (prs.map fun pr =>
          ((pairA (witL bb pr.1) (witL bb pr.2) a b : ℝ) / 2)).sum * y a * y b := by
      rw [sum_comm]; exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    have hdiag : ∑ a ∈ range n, ∑ b ∈ range n,
        (if a = b ∧ (yKind a = 2 ∨ yKind a = 3) then 2 * (β (yBody a) : ℝ) else 0) * y a * y b =
        2 * ∑ a ∈ range n, (β (yBody a) : ℝ) * (if yKind a = 2 ∨ yKind a = 3 then y a ^ 2 else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun a ha => ?_
      rw [sum_eq_single a]
      · split_ifs with h1 h2 h2 <;> simp_all <;> ring
      · intro b _ hb; rw [if_neg (by tauto)]; ring
      · intro h; exact absurd ha h
    have hexp : ∀ a b, ((prs.map fun pr => (((pairA (witL bb pr.1) (witL bb pr.2) a b : ℝ) +
        (pairA (witL bb pr.1) (witL bb pr.2) b a : ℝ)) / 2)).sum +
        (if a = b ∧ (yKind a = 2 ∨ yKind a = 3) then 2 * (β (yBody a) : ℝ) else 0)) * y a * y b =
        (prs.map fun pr => ((pairA (witL bb pr.1) (witL bb pr.2) a b : ℝ) / 2)).sum * y a * y b +
        (prs.map fun pr => ((pairA (witL bb pr.1) (witL bb pr.2) b a : ℝ) / 2)).sum * y a * y b +
        (if a = b ∧ (yKind a = 2 ∨ yKind a = 3) then 2 * (β (yBody a) : ℝ) else 0) * y a * y b := by
      intro a b
      rw [show (fun pr : Wit × Wit => (((pairA (witL bb pr.1) (witL bb pr.2) a b : ℝ) +
          (pairA (witL bb pr.1) (witL bb pr.2) b a : ℝ)) / 2)) =
          fun pr => ((pairA (witL bb pr.1) (witL bb pr.2) a b : ℝ) / 2) +
            ((pairA (witL bb pr.1) (witL bb pr.2) b a : ℝ) / 2) from by funext pr; ring]
      rw [list_sum_add]; ring
    simp_rw [hexp, sum_add_distrib]
    rw [hsym, hdiag]; ring
  rw [hsplit_g, hsplit_H]
  unfold betaSum
  simp only [mul_add, sum_add_distrib]
  ring

/-! ## The β-terms vanish at real placements -/

lemma sum_range_four_blocks (n : ℕ) (g : ℕ → ℝ) :
    ∑ x ∈ range (4 * n), g x = ∑ m ∈ range n, (g (4 * m) + g (4 * m + 1) + g (4 * m + 2) + g (4 * m + 3)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 * n + 4 by ring, sum_range_add, ih, sum_range_succ]
    simp [sum_range_succ]

lemma yKind_block (m j : ℕ) (hj : j < 4) : yKind (2 + 4 * m + j) = j ∧ yBody (2 + 4 * m + j) = m + 2 := by
  unfold yKind yBody
  rw [if_neg (by omega), if_neg (by omega)]
  constructor <;> omega

/-- `2C + C² + S² = 0` for `C = ⟨u(m), u(s)⟩ − 1`, `S = det(u(m), u(s))`. -/
lemma two_C_add_sq (lo hi : ℕ → ℚ) (p : ℕ → ℝ) {i : ℕ} (hi2 : 2 ≤ i) :
    2 * yAt lo hi p (yC i) + yAt lo hi p (yC i) ^ 2 + yAt lo hi p (yS i) ^ 2 = 0 := by
  obtain ⟨kC, bC⟩ := yKind_yBody_C hi2
  obtain ⟨kS, bS'⟩ := yKind_yBody_S hi2
  simp only [yAt, kC, bC, kS, bS', bodyBox_M_cast lo hi hi2, dot2R, det2R]
  have := dot_sq_add_det_sq (((lo (bS i) + hi (bS i)) / 2 : ℚ) : ℝ) (p (bS i))
  nlinarith [this]

lemma betaSum_zero (lo hi : ℕ → ℚ) (p : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k) (β : ℕ → ℚ) :
    betaSum (4 * k - 2) β (yAt lo hi p) = 0 := by
  unfold betaSum
  rw [show 4 * k - 2 = 2 + 4 * (k - 1) by omega, sum_range_add, sum_range_four_blocks]
  have h01 : ∑ x ∈ range 2, (β (yBody x) : ℝ) * ((if yKind x = 2 then 2 * yAt lo hi p x else 0) +
      (if yKind x = 2 ∨ yKind x = 3 then yAt lo hi p x ^ 2 else 0)) = 0 := by
    simp [sum_range_succ, yKind]
  rw [h01, zero_add]
  refine sum_eq_zero fun m _ => ?_
  have K0 : yKind (2 + 4 * m) = 0 := by unfold yKind; rw [if_neg (by omega)]; omega
  have K1 : yKind (2 + (4 * m + 1)) = 1 := by unfold yKind; rw [if_neg (by omega)]; omega
  have K2 : yKind (2 + (4 * m + 2)) = 2 := by unfold yKind; rw [if_neg (by omega)]; omega
  have K3 : yKind (2 + (4 * m + 3)) = 3 := by unfold yKind; rw [if_neg (by omega)]; omega
  have B2 : yBody (2 + (4 * m + 2)) = m + 2 := by unfold yBody; rw [if_neg (by omega)]; omega
  have B3 : yBody (2 + (4 * m + 3)) = m + 2 := by unfold yBody; rw [if_neg (by omega)]; omega
  have e2 : 2 + (4 * m + 2) = yC (m + 2) := by simp [yC]; omega
  have e3 : 2 + (4 * m + 3) = yS (m + 2) := by simp [yS]; omega
  have hz := two_C_add_sq lo hi p (by omega : 2 ≤ m + 2)
  simp only [K0, K1, K2, K3, B2, B3, show (0 : ℕ) ≠ 2 from by decide, show (1 : ℕ) ≠ 2 from by decide,
    show (1 : ℕ) ≠ 3 from by decide, show (0 : ℕ) ≠ 3 from by decide, show (3 : ℕ) ≠ 2 from by decide,
    false_or, or_false, if_false, if_true, true_or, or_true, add_zero, zero_add, mul_zero]
  rw [e2, e3]
  linear_combination (β (m + 2) : ℝ) * hz

/-! ## The PSD certificate and the quadratic bound (range form) -/

lemma qf_range_LDL (n : ℕ) (N L : ℕ → ℕ → ℝ) (D : ℕ → ℝ)
    (hN : ∀ a ∈ range n, ∀ b ∈ range n, N a b = ∑ c ∈ range n, L a c * D c * L b c) (v : ℕ → ℝ) :
    ∑ a ∈ range n, ∑ b ∈ range n, N a b * v a * v b = ∑ c ∈ range n, D c * (∑ a ∈ range n, v a * L a c) ^ 2 := by
  have h1 : ∀ a ∈ range n, ∀ b ∈ range n, N a b * v a * v b = ∑ c ∈ range n, D c * (v a * L a c) * (v b * L b c) := by
    intro a ha b hb
    rw [hN a ha b hb, sum_mul, sum_mul]
    exact sum_congr rfl fun c _ => by ring
  have h2 : ∀ c, D c * (∑ a ∈ range n, v a * L a c) ^ 2 =
      ∑ a ∈ range n, ∑ b ∈ range n, D c * (v a * L a c) * (v b * L b c) := by
    intro c
    rw [sq, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun a _ => by rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => h1 a ha b hb]
  simp_rw [h2]
  calc ∑ a ∈ range n, ∑ b ∈ range n, ∑ c ∈ range n, D c * (v a * L a c) * (v b * L b c)
      = ∑ a ∈ range n, ∑ c ∈ range n, ∑ b ∈ range n, D c * (v a * L a c) * (v b * L b c) :=
        sum_congr rfl fun a _ => sum_comm
    _ = ∑ c ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, D c * (v a * L a c) * (v b * L b c) := sum_comm

/-- **A passing PSD check gives a positive semidefinite matrix.** -/
lemma psd_of_psdOK {n : ℕ} {N : ℕ → ℕ → ℚ} (h : psdOK n N = true) (v : ℕ → ℝ) :
    0 ≤ ∑ a ∈ range n, ∑ b ∈ range n, (N a b : ℝ) * v a * v b := by
  simp only [psdOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hD, hN⟩ := h
  set L := (ldl n N).1
  set D := (ldl n N).2
  have hN' : ∀ a ∈ range n, ∀ b ∈ range n, (N a b : ℝ) = ∑ c ∈ range n, (L a c : ℝ) * (D c : ℝ) * (L b c : ℝ) := by
    intro a ha b hb
    rw [mem_range] at ha hb
    have := hN a ha b hb
    rw [this]; push_cast; rfl
  rw [qf_range_LDL n (fun a b => (N a b : ℝ)) (fun a c => (L a c : ℝ)) (fun c => (D c : ℝ)) hN' v]
  refine sum_nonneg fun c hc => mul_nonneg ?_ (sq_nonneg _)
  rw [mem_range] at hc
  exact_mod_cast hD c hc

/-- **Quadratic lower bound on a box (range form).** -/
lemma quad_lower_psd (n : ℕ) (c : ℝ) (g σ y y0 w : ℕ → ℝ) (H : ℕ → ℕ → ℝ)
    (hsymm : ∀ a b, H a b = H b a)
    (hpsd : ∀ v : ℕ → ℝ, 0 ≤ ∑ a ∈ range n, ∑ b ∈ range n, (H a b + if a = b then σ a else 0) * v a * v b)
    (hσ : ∀ a ∈ range n, 0 ≤ σ a) (hy : ∀ a ∈ range n, |y a - y0 a| ≤ w a) :
    c + ∑ a ∈ range n, g a * y0 a + (∑ a ∈ range n, ∑ b ∈ range n, H a b * y0 a * y0 b) / 2
      - ∑ a ∈ range n, |g a + ∑ b ∈ range n, H a b * y0 b| * w a - (∑ a ∈ range n, σ a * w a ^ 2) / 2 ≤
    c + ∑ a ∈ range n, g a * y a + (∑ a ∈ range n, ∑ b ∈ range n, H a b * y a * y b) / 2 := by
  set Δ : ℕ → ℝ := fun a => y a - y0 a with hΔ
  have hw0 : ∀ a ∈ range n, 0 ≤ w a := fun a ha => (abs_nonneg _).trans (hy a ha)
  -- expansion of the symmetric quadratic around y0
  have hexp : ∑ a ∈ range n, ∑ b ∈ range n, H a b * y a * y b =
      ∑ a ∈ range n, ∑ b ∈ range n, H a b * y0 a * y0 b + 2 * ∑ a ∈ range n, (∑ b ∈ range n, H a b * y0 b) * Δ a +
        ∑ a ∈ range n, ∑ b ∈ range n, H a b * Δ a * Δ b := by
    have key : ∀ a b, H a b * y a * y b = H a b * y0 a * y0 b + H a b * y0 b * Δ a + H a b * y0 a * Δ b +
        H a b * Δ a * Δ b := by intro a b; simp only [hΔ]; ring
    simp_rw [key, sum_add_distrib]
    have hswap : ∑ a ∈ range n, ∑ b ∈ range n, H a b * y0 a * Δ b =
        ∑ a ∈ range n, ∑ b ∈ range n, H a b * y0 b * Δ a := by
      rw [sum_comm]; exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by rw [hsymm b a]
    rw [hswap]
    have hm : ∑ a ∈ range n, (∑ b ∈ range n, H a b * y0 b) * Δ a = ∑ a ∈ range n, ∑ b ∈ range n, H a b * y0 b * Δ a := by
      exact sum_congr rfl fun a _ => by rw [sum_mul]
    rw [hm]; ring
  have hgy : ∑ a ∈ range n, g a * y a = ∑ a ∈ range n, g a * y0 a + ∑ a ∈ range n, g a * Δ a := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun a _ => by simp only [hΔ]; ring
  have hlin : -∑ a ∈ range n, |g a + ∑ b ∈ range n, H a b * y0 b| * w a ≤
      ∑ a ∈ range n, (g a + ∑ b ∈ range n, H a b * y0 b) * Δ a := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun a ha => ?_
    have h2 : -(|g a + ∑ b ∈ range n, H a b * y0 b| * |Δ a|) ≤ (g a + ∑ b ∈ range n, H a b * y0 b) * Δ a := by
      rw [← abs_mul]; exact neg_abs_le _
    have h3 := mul_le_mul_of_nonneg_left (hy a ha) (abs_nonneg (g a + ∑ b ∈ range n, H a b * y0 b))
    linarith
  have hquad : -(∑ a ∈ range n, σ a * w a ^ 2) ≤ ∑ a ∈ range n, ∑ b ∈ range n, H a b * Δ a * Δ b := by
    have h1 := hpsd Δ
    have hsplit : ∑ a ∈ range n, ∑ b ∈ range n, (H a b + if a = b then σ a else 0) * Δ a * Δ b =
        ∑ a ∈ range n, ∑ b ∈ range n, H a b * Δ a * Δ b + ∑ a ∈ range n, σ a * Δ a ^ 2 := by
      have e : ∀ a b, (H a b + if a = b then σ a else 0) * Δ a * Δ b =
          H a b * Δ a * Δ b + (if a = b then σ a else 0) * Δ a * Δ b := by intro a b; ring
      simp_rw [e, sum_add_distrib]
      congr 1
      refine sum_congr rfl fun a ha => ?_
      rw [sum_eq_single a]
      · simp; ring
      · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
      · intro h; exact absurd ha h
    have h2 : ∑ a ∈ range n, σ a * Δ a ^ 2 ≤ ∑ a ∈ range n, σ a * w a ^ 2 := by
      refine sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ (hσ a ha)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hy a ha) 2
    linarith
  have hsplit2 : ∑ a ∈ range n, (g a + ∑ b ∈ range n, H a b * y0 b) * Δ a =
      ∑ a ∈ range n, g a * Δ a + ∑ a ∈ range n, (∑ b ∈ range n, H a b * y0 b) * Δ a := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun a _ => by ring
  rw [hgy, hexp]
  linarith

lemma fanQuad_H_symm (bb : ℕ → BodyBox) (W : List Wit) (β : ℕ → ℚ) (a b : ℕ) :
    (fanQuad bb W β).H a b = (fanQuad bb W β).H b a := by
  unfold fanQuad
  simp only []
  congr 1
  · congr 1
    apply List.map_congr_left
    rintro ⟨w, w'⟩ _
    simp only []
    ring
  · by_cases h : a = b
    · subst h; rfl
    · rw [if_neg (fun h' => h h'.1), if_neg (fun h' => h h'.1.symm)]

/-! ## Soundness of the leaf check (algebraic part) -/

/-- What a passing leaf check guarantees at every placement of its box. -/
structure LeafFacts (ns : List ℕ) (vt : VertTable) (lo hi : ℕ → ℚ) (W : List Wit) (z : ℚ × ℚ) (p : ℕ → ℝ)
    (τ : ℚ) : Prop where
  dets : ∀ pr ∈ cycPairs W, 0 < det2R (subR (witPos p pr.1) (castP z)) (subR (witPos p pr.2) (castP z))
  area : (τ : ℝ) < fanAreaR p W
  mem : ∀ w ∈ W, w.body ≤ ns.length ∧ memOK ns vt w = true
  zmem : dot2 z z < 1 / 4
  wind : windOK (bodyBox lo hi) z W = true
  len : 3 ≤ W.length
  k2 : 2 ≤ ns.length
  rows : ∀ pr ∈ cycPairs W, 0 < fanRow (4 * ns.length - 2) (bodyBox lo hi) z pr.1 pr.2
  box : ∀ v ∈ range (4 * ns.length - 2),
    |yAt lo hi p v - (yCentre (bodyBox lo hi) v : ℝ)| ≤ (yHalf (bodyBox lo hi) v : ℝ)
  lin_eq : ∀ w ∈ W, witPos p w = lin (4 * ns.length - 2) (castP (witX0 (bodyBox lo hi) w))
    (fun v => castP (witL (bodyBox lo hi) w v)) (yAt lo hi p)

theorem leafOK_sound {ns : List ℕ} {vt : VertTable} {τ : ℚ} {lo hi : ℕ → ℚ} {W : List Wit} {z : ℚ × ℚ}
    {β σ : ℕ → ℚ} (h : leafOK ns vt τ lo hi W z β σ = true) (p : ℕ → ℝ)
    (hp : ∀ a, a < 3 * ns.length - 1 → (lo a : ℝ) ≤ p a ∧ p a ≤ hi a) :
    LeafFacts ns vt lo hi W z p τ := by
  simp only [leafOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsok, hk⟩, hlen⟩, hmem⟩, hz⟩, hrows⟩, hwind⟩, hσ⟩, hpsd⟩, hbound⟩ := h
  set k := ns.length with hkdef
  have hs : ∀ i, 2 ≤ i → i ≤ k → (bodyBox lo hi i).sOK = true := fun i _ hi => hsok i (by omega)
  have hW : ∀ w ∈ W, w.body ≤ k := fun w hw => (hmem w hw).1
  refine ⟨?_, ?_, fun w hw => hmem w hw, hz, hwind, hlen, hk, hrows, yAt_mem_box lo hi p hs hp,
    fun w hw => witPos_eq_lin lo hi p hk w (hW w hw)⟩
  · -- determinants
    intro pr hpr
    obtain ⟨h1, h2⟩ := mem_cycPairs_body hW pr hpr
    exact fanRow_sound lo hi p hk hs hp z pr.1 pr.2 h1 h2 (hrows pr hpr)
  · -- the fan area
    set bb := bodyBox lo hi
    set Q := fanQuad bb W β
    set n := 4 * k - 2
    have heval := fanQuad_eval lo hi p hk W hW β
    rw [betaSum_zero lo hi p hk β, add_zero] at heval
    rw [← heval]
    have hq := quad_lower_psd n (Q.F0 : ℝ) (fun a => (Q.g a : ℝ)) (fun a => (σ a : ℝ)) (yAt lo hi p)
      (fun a => (yCentre bb a : ℝ)) (fun a => (yHalf bb a : ℝ)) (fun a b => (Q.H a b : ℝ))
      (fun a b => by show ((Q.H a b : ℚ) : ℝ) = ((Q.H b a : ℚ) : ℝ); rw [fanQuad_H_symm])
      (fun v => by
        have := psd_of_psdOK hpsd v
        refine le_of_le_of_eq this (sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_)
        push_cast
        split_ifs <;> simp)
      (fun a ha => by rw [mem_range] at ha; exact_mod_cast hσ a ha)
      (yAt_mem_box lo hi p hs hp)
    refine lt_of_lt_of_le ?_ hq
    have hcast : ((fanLower n bb Q σ : ℚ) : ℝ) =
        (Q.F0 : ℝ) + ∑ a ∈ range n, (Q.g a : ℝ) * (yCentre bb a : ℝ) +
          (∑ a ∈ range n, ∑ b ∈ range n, (Q.H a b : ℝ) * (yCentre bb a : ℝ) * (yCentre bb b : ℝ)) / 2 -
          ∑ a ∈ range n, |(Q.g a : ℝ) + ∑ b ∈ range n, (Q.H a b : ℝ) * (yCentre bb b : ℝ)| * (yHalf bb a : ℝ) -
          (∑ a ∈ range n, (σ a : ℝ) * (yHalf bb a : ℝ) ^ 2) / 2 := by
      simp [fanLower]
    rw [← hcast]
    exact_mod_cast hbound

/-! ## Combination leaves -/

/-- **Affine minorant of a quadratic** from a PSD certificate. -/
lemma quad_taylor_psd (n : ℕ) (c : ℝ) (g σ y y0 w : ℕ → ℝ) (H : ℕ → ℕ → ℝ)
    (hsymm : ∀ a b, H a b = H b a)
    (hpsd : ∀ v : ℕ → ℝ, 0 ≤ ∑ a ∈ range n, ∑ b ∈ range n, (H a b + if a = b then σ a else 0) * v a * v b)
    (hσ : ∀ a ∈ range n, 0 ≤ σ a) (hy : ∀ a ∈ range n, |y a - y0 a| ≤ w a) :
    c + ∑ a ∈ range n, g a * y0 a + (∑ a ∈ range n, ∑ b ∈ range n, H a b * y0 a * y0 b) / 2
      - (∑ a ∈ range n, σ a * w a ^ 2) / 2
      + ∑ a ∈ range n, (g a + ∑ b ∈ range n, H a b * y0 b) * (y a - y0 a) ≤
    c + ∑ a ∈ range n, g a * y a + (∑ a ∈ range n, ∑ b ∈ range n, H a b * y a * y b) / 2 := by
  set Δ : ℕ → ℝ := fun a => y a - y0 a with hΔ
  have hexp : ∑ a ∈ range n, ∑ b ∈ range n, H a b * y a * y b =
      ∑ a ∈ range n, ∑ b ∈ range n, H a b * y0 a * y0 b + 2 * ∑ a ∈ range n, (∑ b ∈ range n, H a b * y0 b) * Δ a +
        ∑ a ∈ range n, ∑ b ∈ range n, H a b * Δ a * Δ b := by
    have key : ∀ a b, H a b * y a * y b = H a b * y0 a * y0 b + H a b * y0 b * Δ a + H a b * y0 a * Δ b +
        H a b * Δ a * Δ b := by intro a b; simp only [hΔ]; ring
    simp_rw [key, sum_add_distrib]
    have hswap : ∑ a ∈ range n, ∑ b ∈ range n, H a b * y0 a * Δ b =
        ∑ a ∈ range n, ∑ b ∈ range n, H a b * y0 b * Δ a := by
      rw [sum_comm]; exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by rw [hsymm b a]
    rw [hswap]
    have hm : ∑ a ∈ range n, (∑ b ∈ range n, H a b * y0 b) * Δ a =
        ∑ a ∈ range n, ∑ b ∈ range n, H a b * y0 b * Δ a := by
      exact sum_congr rfl fun a _ => by rw [sum_mul]
    rw [hm]; ring
  have hgy : ∑ a ∈ range n, g a * y a = ∑ a ∈ range n, g a * y0 a + ∑ a ∈ range n, g a * Δ a := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun a _ => by simp only [hΔ]; ring
  have hquad : -(∑ a ∈ range n, σ a * w a ^ 2) ≤ ∑ a ∈ range n, ∑ b ∈ range n, H a b * Δ a * Δ b := by
    have h1 := hpsd Δ
    have hsplit : ∑ a ∈ range n, ∑ b ∈ range n, (H a b + if a = b then σ a else 0) * Δ a * Δ b =
        ∑ a ∈ range n, ∑ b ∈ range n, H a b * Δ a * Δ b + ∑ a ∈ range n, σ a * Δ a ^ 2 := by
      have e : ∀ a b, (H a b + if a = b then σ a else 0) * Δ a * Δ b =
          H a b * Δ a * Δ b + (if a = b then σ a else 0) * Δ a * Δ b := by intro a b; ring
      simp_rw [e, sum_add_distrib]
      congr 1
      refine sum_congr rfl fun a ha => ?_
      rw [sum_eq_single a]
      · simp; ring
      · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
      · intro h; exact absurd ha h
    have h2 : ∑ a ∈ range n, σ a * Δ a ^ 2 ≤ ∑ a ∈ range n, σ a * w a ^ 2 := by
      refine sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ (hσ a ha)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hy a ha) 2
    linarith
  have hsplit2 : ∑ a ∈ range n, (g a + ∑ b ∈ range n, H a b * y0 b) * Δ a =
      ∑ a ∈ range n, g a * Δ a + ∑ a ∈ range n, (∑ b ∈ range n, H a b * y0 b) * Δ a := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun a _ => by ring
  rw [hgy, hexp]
  linarith

/-- What a passing fan check guarantees at a placement of the box (the geometric part). -/
structure FanFacts (ns : List ℕ) (vt : VertTable) (lo hi : ℕ → ℚ) (W : List Wit) (z : ℚ × ℚ) (p : ℕ → ℝ) :
    Prop where
  mem : ∀ w ∈ W, w.body ≤ ns.length ∧ memOK ns vt w = true
  zmem : dot2 z z < 1 / 4
  wind : windOK (bodyBox lo hi) z W = true
  len : 3 ≤ W.length
  rows : ∀ pr ∈ cycPairs W, 0 < fanRow (4 * ns.length - 2) (bodyBox lo hi) z pr.1 pr.2
  box : ∀ v ∈ range (4 * ns.length - 2),
    |yAt lo hi p v - (yCentre (bodyBox lo hi) v : ℝ)| ≤ (yHalf (bodyBox lo hi) v : ℝ)
  lin_eq : ∀ w ∈ W, witPos p w = lin (4 * ns.length - 2) (castP (witX0 (bodyBox lo hi) w))
    (fun v => castP (witL (bodyBox lo hi) w v)) (yAt lo hi p)

lemma LeafFacts.toFanFacts {ns : List ℕ} {vt : VertTable} {lo hi : ℕ → ℚ} {W : List Wit} {z : ℚ × ℚ}
    {p : ℕ → ℝ} {τ : ℚ} (F : LeafFacts ns vt lo hi W z p τ) : FanFacts ns vt lo hi W z p :=
  ⟨F.mem, F.zmem, F.wind, F.len, F.rows, F.box, F.lin_eq⟩

/-- **A passing fan check** gives the fan facts and the affine minorant of the fan area on the box. -/
theorem fanOK_sound {ns : List ℕ} {vt : VertTable} {lo hi : ℕ → ℚ} {W : List Wit} {z : ℚ × ℚ}
    {β σ : ℕ → ℚ} (h : fanOK ns vt lo hi W z β σ = true) (hk : 2 ≤ ns.length)
    (hs : ∀ i, 2 ≤ i → i ≤ ns.length → (bodyBox lo hi i).sOK = true) (p : ℕ → ℝ)
    (hp : ∀ a, a < 3 * ns.length - 1 → (lo a : ℝ) ≤ p a ∧ p a ≤ hi a) :
    FanFacts ns vt lo hi W z p ∧
      ((fanA (4 * ns.length - 2) (bodyBox lo hi) (fanQuad (bodyBox lo hi) W β) σ : ℚ) : ℝ) +
        ∑ a ∈ range (4 * ns.length - 2),
          ((fanG (4 * ns.length - 2) (bodyBox lo hi) (fanQuad (bodyBox lo hi) W β) a : ℚ) : ℝ) *
            (yAt lo hi p a - (yCentre (bodyBox lo hi) a : ℝ)) ≤ fanAreaR p W := by
  simp only [fanOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hlen, hmem⟩, hz⟩, hrows⟩, hwind⟩, hσ⟩, hpsd⟩ := h
  set k := ns.length with hkdef
  have hW : ∀ w ∈ W, w.body ≤ k := fun w hw => (hmem w hw).1
  refine ⟨⟨fun w hw => hmem w hw, hz, hwind, hlen, hrows, yAt_mem_box lo hi p hs hp,
    fun w hw => witPos_eq_lin lo hi p hk w (hW w hw)⟩, ?_⟩
  set bb := bodyBox lo hi
  set Q := fanQuad bb W β
  set n := 4 * k - 2
  have heval := fanQuad_eval lo hi p hk W hW β
  rw [betaSum_zero lo hi p hk β, add_zero] at heval
  rw [← heval]
  have hq := quad_taylor_psd n (Q.F0 : ℝ) (fun a => (Q.g a : ℝ)) (fun a => (σ a : ℝ)) (yAt lo hi p)
    (fun a => (yCentre bb a : ℝ)) (fun a => (yHalf bb a : ℝ)) (fun a b => (Q.H a b : ℝ))
    (fun a b => by show ((Q.H a b : ℚ) : ℝ) = ((Q.H b a : ℚ) : ℝ); rw [fanQuad_H_symm])
    (fun v => by
      have := psd_of_psdOK hpsd v
      refine le_of_le_of_eq this (sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_)
      push_cast
      split_ifs <;> simp)
    (fun a ha => by rw [mem_range] at ha; exact_mod_cast hσ a ha)
    (yAt_mem_box lo hi p hs hp)
  refine le_of_eq_of_le ?_ hq
  simp only [fanA, fanG]
  push_cast
  ring

end LebesgueCover.Cert
