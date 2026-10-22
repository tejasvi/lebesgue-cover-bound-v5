import LebesgueCover.Trig.Trig
import LebesgueCover.Trig.FixSound

/-!
# Soundness of `ZZChk/Trig.lean`: π, and cos/sin at rational multiples of π
-/

namespace LebTrig.Sound

open LebTrig Real

/-! ## π -/

lemma PLO_le_pi : (PLO : ℝ) / 2 ^ PIS ≤ π := by
  have h : (PLO : ℝ) / 2 ^ PIS ≤ 3.14159265358979323846 := by
    unfold PLO PIS; norm_num
  linarith [Real.pi_gt_d20]

lemma pi_le_PHI : π ≤ (PHI : ℝ) / 2 ^ PIS := by
  have h : (3.14159265358979323847 : ℝ) ≤ (PHI : ℝ) / 2 ^ PIS := by
    unfold PHI PIS; norm_num
  linarith [Real.pi_lt_d20]

lemma piEncl_encl : Encl PR piEncl π := by
  have e : (2 : ℝ) ^ PR = 2 ^ (PR - PIS) * 2 ^ PIS := by unfold PR PIS; norm_num
  have h1 := PLO_le_pi
  have h2 := pi_le_PHI
  rw [div_le_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (by positivity)] at h2
  unfold piEncl Encl
  simp only [Int.ofNat_eq_natCast]
  push_cast
  rw [e]
  constructor <;> nlinarith [pow_pos (two_pos (α := ℝ)) (PR - PIS)]

/-! ## Taylor sums -/

/-- `∑_{k<17} (-1)^k x^(2k)/(2k)!`. -/
noncomputable def cosT (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 17, (-1) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)

/-- `∑_{k<17} (-1)^k x^(2k+1)/(2k+1)!`. -/
noncomputable def sinT (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 17, (-1) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

lemma factorial_ge_pow {m : ℕ} (hm : 1 ≤ m) (n : ℕ) : (m.factorial : ℝ) * 2 ^ n ≤ ((m + 2 * n).factorial : ℝ) := by
  have h := @Nat.factorial_mul_pow_le_factorial m (2 * n)
  have h2 : 2 ^ n ≤ (m + 1) ^ (2 * n) := by
    calc 2 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by norm_num) n
      _ = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
      _ ≤ (m + 1) ^ (2 * n) := Nat.pow_le_pow_left (by omega) _
  have h3 : m.factorial * 2 ^ n ≤ (m + 2 * n).factorial :=
    le_trans (Nat.mul_le_mul_left _ h2) h
  exact_mod_cast h3

/-- Geometric tail: `|∑_{n} f(n + N)| ≤ 2c` if `|f(n+N)| ≤ c (1/2)^n`. -/
lemma abs_tail_le {f : ℕ → ℝ} {S c : ℝ} (hS : HasSum f S) (N : ℕ)
    (hb : ∀ n, |f (n + N)| ≤ c * (1 / 2) ^ n) :
    |S - ∑ i ∈ Finset.range N, f i| ≤ 2 * c := by
  have h1 := (hasSum_nat_add_iff' N).2 hS
  have hg : HasSum (fun n : ℕ => c * (1 / 2 : ℝ) ^ n) (c * 2) := by
    have := (hasSum_geometric_two).mul_left c
    simpa using this
  have hup := hasSum_le (fun n => le_of_abs_le (hb n)) h1 hg
  have hlo := hasSum_le (fun n => neg_le_of_abs_le (hb n)) hg.neg h1
  rw [abs_le]
  constructor <;> linarith

lemma abs_cos_sub_cosT {x : ℝ} (hx : |x| ≤ 1) : |cos x - cosT x| ≤ 2 * (|x| ^ 34 / (34).factorial) := by
  refine abs_tail_le (Real.hasSum_cos x) 17 fun n => ?_
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < ((2 * (n + 17)).factorial : ℝ))]
  have hf := factorial_ge_pow (m := 34) (by norm_num) n
  rw [show 34 + 2 * n = 2 * (n + 17) by ring] at hf
  have hx0 := abs_nonneg x
  have hpow : |x| ^ (2 * (n + 17)) ≤ |x| ^ 34 := by
    apply pow_le_pow_of_le_one hx0 hx; omega
  rw [div_le_iff₀ (by positivity)]
  calc |x| ^ (2 * (n + 17)) ≤ |x| ^ 34 := hpow
    _ = |x| ^ 34 / (34).factorial * ((34).factorial * 2 ^ n) * (1 / 2) ^ n := by
        field_simp; rw [mul_assoc, ← mul_pow]; norm_num
    _ ≤ |x| ^ 34 / (34).factorial * ((2 * (n + 17)).factorial) * (1 / 2) ^ n := by
        gcongr
    _ = _ := by ring

lemma abs_sin_sub_sinT {x : ℝ} (hx : |x| ≤ 1) : |sin x - sinT x| ≤ 2 * (|x| ^ 35 / (35).factorial) := by
  refine abs_tail_le (Real.hasSum_sin x) 17 fun n => ?_
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < ((2 * (n + 17) + 1).factorial : ℝ))]
  have hf := factorial_ge_pow (m := 35) (by norm_num) n
  rw [show 35 + 2 * n = 2 * (n + 17) + 1 by ring] at hf
  have hx0 := abs_nonneg x
  have hpow : |x| ^ (2 * (n + 17) + 1) ≤ |x| ^ 35 := by
    apply pow_le_pow_of_le_one hx0 hx; omega
  rw [div_le_iff₀ (by positivity)]
  calc |x| ^ (2 * (n + 17) + 1) ≤ |x| ^ 35 := hpow
    _ = |x| ^ 35 / (35).factorial * ((35).factorial * 2 ^ n) * (1 / 2) ^ n := by
        field_simp; rw [mul_assoc, ← mul_pow]; norm_num
    _ ≤ |x| ^ 35 / (35).factorial * ((2 * (n + 17) + 1).factorial) * (1 / 2) ^ n := by
        gcongr
    _ = _ := by ring

/-- The remainder is below `2^-135` for `|x| ≤ 4/5`. -/
lemma cos_rem_small {x : ℝ} (hx : |x| ≤ 4 / 5) : |cos x - cosT x| ≤ 1 / 2 ^ 135 := by
  refine (abs_cos_sub_cosT (hx.trans (by norm_num))).trans ?_
  have : |x| ^ 34 ≤ (4 / 5 : ℝ) ^ 34 := pow_le_pow_left₀ (abs_nonneg x) hx 34
  calc 2 * (|x| ^ 34 / (34).factorial) ≤ 2 * ((4 / 5 : ℝ) ^ 34 / (34).factorial) := by gcongr
    _ ≤ 1 / 2 ^ 135 := by rw [Nat.factorial]; norm_num [Nat.factorial]

lemma sin_rem_small {x : ℝ} (hx : |x| ≤ 4 / 5) : |sin x - sinT x| ≤ 1 / 2 ^ 135 := by
  refine (abs_sin_sub_sinT (hx.trans (by norm_num))).trans ?_
  have : |x| ^ 35 ≤ (4 / 5 : ℝ) ^ 35 := pow_le_pow_left₀ (abs_nonneg x) hx 35
  calc 2 * (|x| ^ 35 / (35).factorial) ≤ 2 * ((4 / 5 : ℝ) ^ 35 / (35).factorial) := by gcongr
    _ ≤ 1 / 2 ^ 135 := by rw [Nat.factorial]; norm_num [Nat.factorial]

/-! ## The exact Horner sums -/

/-- Value of a fraction `(num, den)`. -/
noncomputable def fval (p : ℤ × ℕ) : ℝ := (p.1 : ℝ) / p.2

/-- Horner recursion of the cosine partial sums (in `x² = x2`). -/
noncomputable def hcos (x2 : ℝ) : ℕ → ℝ → ℝ
  | 0, v => v
  | m + 1, v => hcos x2 m (1 - x2 * v / ((2 * m + 1) * (2 * m + 2)))

/-- Horner recursion of the sine partial sums divided by `x`. -/
noncomputable def hsin (x2 : ℝ) : ℕ → ℝ → ℝ
  | 0, v => v
  | m + 1, v => hsin x2 m (1 - x2 * v / ((2 * m + 2) * (2 * m + 3)))

lemma cosLoop_spec (y z : ℕ) (hz : 0 < z) : ∀ (m : ℕ) (acc : ℤ × ℕ), 0 < acc.2 →
    0 < (cosLoop y z m acc).2 ∧ fval (cosLoop y z m acc) = hcos ((y : ℝ) / z) m (fval acc) := by
  intro m
  induction m with
  | zero => intro acc h; exact ⟨h, rfl⟩
  | succ m ih =>
    intro acc h
    simp only [cosLoop]
    have hq : 0 < z * ((2 * m + 1) * (2 * m + 2)) * acc.2 := by positivity
    obtain ⟨h1, h2⟩ := ih (Int.ofNat (z * ((2 * m + 1) * (2 * m + 2)) * acc.2) - Int.ofNat y * acc.1,
      z * ((2 * m + 1) * (2 * m + 2)) * acc.2) hq
    refine ⟨h1, ?_⟩
    rw [h2, hcos]
    congr 1
    simp only [fval, Int.ofNat_eq_natCast]
    have hz' : (0 : ℝ) < z := by exact_mod_cast hz
    have ha : (0 : ℝ) < acc.2 := by exact_mod_cast h
    push_cast
    field_simp

lemma sinLoop_spec (y z : ℕ) (hz : 0 < z) : ∀ (m : ℕ) (acc : ℤ × ℕ), 0 < acc.2 →
    0 < (sinLoop y z m acc).2 ∧ fval (sinLoop y z m acc) = hsin ((y : ℝ) / z) m (fval acc) := by
  intro m
  induction m with
  | zero => intro acc h; exact ⟨h, rfl⟩
  | succ m ih =>
    intro acc h
    simp only [sinLoop]
    have hq : 0 < z * ((2 * m + 2) * (2 * m + 3)) * acc.2 := by positivity
    obtain ⟨h1, h2⟩ := ih (Int.ofNat (z * ((2 * m + 2) * (2 * m + 3)) * acc.2) - Int.ofNat y * acc.1,
      z * ((2 * m + 2) * (2 * m + 3)) * acc.2) hq
    refine ⟨h1, ?_⟩
    rw [h2, hsin]
    congr 1
    simp only [fval, Int.ofNat_eq_natCast]
    have hz' : (0 : ℝ) < z := by exact_mod_cast hz
    have ha : (0 : ℝ) < acc.2 := by exact_mod_cast h
    push_cast
    field_simp

lemma hcos_eq (x2 : ℝ) : ∀ (m : ℕ) (v : ℝ), hcos x2 m v =
    ∑ k ∈ Finset.range m, (-1) ^ k * x2 ^ k / ((2 * k).factorial : ℝ) +
      (-1) ^ m * x2 ^ m / ((2 * m).factorial : ℝ) * v := by
  intro m
  induction m with
  | zero => intro v; simp [hcos]
  | succ m ih =>
    intro v
    rw [hcos, ih, Finset.sum_range_succ]
    have hf : ((2 * (m + 1)).factorial : ℝ) = (2 * m).factorial * ((2 * m + 1) * (2 * m + 2)) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [hf]
    have h1 : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

lemma hsin_eq (x2 : ℝ) : ∀ (m : ℕ) (v : ℝ), hsin x2 m v =
    ∑ k ∈ Finset.range m, (-1) ^ k * x2 ^ k / ((2 * k + 1).factorial : ℝ) +
      (-1) ^ m * x2 ^ m / ((2 * m + 1).factorial : ℝ) * v := by
  intro m
  induction m with
  | zero => intro v; simp [hsin]
  | succ m ih =>
    intro v
    rw [hsin, ih, Finset.sum_range_succ]
    have hf : ((2 * (m + 1) + 1).factorial : ℝ) = (2 * m + 1).factorial * ((2 * m + 2) * (2 * m + 3)) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by ring, Nat.factorial_succ,
        show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.factorial_succ]
      push_cast; ring
    rw [hf]
    have h1 : ((2 * m + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

lemma cosSeries_spec (a b : ℕ) (hb : 0 < b) :
    0 < (cosSeries a b).2 ∧ fval (cosSeries a b) = cosT ((a : ℝ) / b) := by
  have hNT : NT - 1 = 16 := rfl
  unfold cosSeries
  rw [hNT]
  obtain ⟨h1, h2⟩ := cosLoop_spec (a * a) (b * b) (by positivity) 16 (1, 1) Nat.one_pos
  refine ⟨h1, ?_⟩
  rw [h2, hcos_eq]
  have hv : fval ((1 : ℤ), (1 : ℕ)) = 1 := by simp [fval]
  rw [hv, mul_one]
  have hx : ((a * a : ℕ) : ℝ) / ((b * b : ℕ) : ℝ) = ((a : ℝ) / b) ^ 2 := by push_cast; ring
  rw [hx]
  unfold cosT
  rw [show (17 : ℕ) = 16 + 1 from rfl, Finset.sum_range_succ _ 16]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_mul]
  · rw [← pow_mul]

lemma sinSeries_spec (a b : ℕ) (hb : 0 < b) :
    0 < (sinSeries a b).2 ∧ fval (sinSeries a b) = sinT ((a : ℝ) / b) := by
  have hNT : NT - 1 = 16 := rfl
  unfold sinSeries
  rw [hNT]
  obtain ⟨h1, h2⟩ := sinLoop_spec (a * a) (b * b) (by positivity) 16 (1, 1) Nat.one_pos
  refine ⟨Nat.mul_pos h1 hb, ?_⟩
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have e : fval ((sinLoop (a * a) (b * b) 16 (1, 1)).1 * Int.ofNat a, (sinLoop (a * a) (b * b) 16 (1, 1)).2 * b)
      = fval (sinLoop (a * a) (b * b) 16 (1, 1)) * ((a : ℝ) / b) := by
    simp only [fval, Int.ofNat_eq_natCast]; push_cast; field_simp
  rw [e, h2, hsin_eq]
  have hv : fval ((1 : ℤ), (1 : ℕ)) = 1 := by simp [fval]
  rw [hv, mul_one]
  have hx : ((a * a : ℕ) : ℝ) / ((b * b : ℕ) : ℝ) = ((a : ℝ) / b) ^ 2 := by push_cast; ring
  rw [hx]
  unfold sinT
  rw [show (17 : ℕ) = 16 + 1 from rfl, Finset.sum_range_succ _ 16, add_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_mul, pow_succ]; ring
  · rw [← pow_mul, pow_succ]; ring

/-! ## Rounding -/

lemma rnd_fst_le {nd : ℤ × ℕ} (hd : 0 < nd.2) {y : ℝ} (h : fval nd - 1 / 2 ^ 135 ≤ y) :
    ((rnd nd).1 : ℝ) ≤ 2 ^ PR * y := by
  unfold rnd
  have h1 := fdiv_le (nd.1 * Int.ofNat ONE) hd
  simp only [Int.ofNat_eq_natCast] at h1 ⊢
  push_cast at h1 ⊢
  rw [ONE_eq] at h1
  have e : (nd.1 : ℝ) * 2 ^ PR / nd.2 = 2 ^ PR * fval nd := by simp only [fval]; ring
  rw [e] at h1
  have h2 : (2 : ℝ) ^ PR * (1 / 2 ^ 135) ≤ 1 := by unfold PR; norm_num
  have h3 := mul_le_mul_of_nonneg_left h (two_pow_pos PR).le
  rw [mul_sub] at h3
  linarith

lemma le_rnd_snd {nd : ℤ × ℕ} (hd : 0 < nd.2) {y : ℝ} (h : y ≤ fval nd + 1 / 2 ^ 135) :
    2 ^ PR * y ≤ ((rnd nd).2 : ℝ) := by
  unfold rnd
  have h1 := le_cdiv (nd.1 * Int.ofNat ONE) hd
  simp only [Int.ofNat_eq_natCast] at h1 ⊢
  push_cast at h1 ⊢
  rw [ONE_eq] at h1
  have e : (nd.1 : ℝ) * 2 ^ PR / nd.2 = 2 ^ PR * fval nd := by simp only [fval]; ring
  rw [e] at h1
  have h2 : (2 : ℝ) ^ PR * (1 / 2 ^ 135) ≤ 1 := by unfold PR; norm_num
  have h3 := mul_le_mul_of_nonneg_left h (two_pow_pos PR).le
  rw [mul_add] at h3
  linarith

/-! ## cos and sin on `[0, π/4]` -/

lemma PHI_div_le : (PHI : ℝ) / 2 ^ PIS ≤ 16 / 5 := by unfold PHI PIS; norm_num

lemma PLO_div_nonneg : (0 : ℝ) ≤ (PLO : ℝ) / 2 ^ PIS := by positivity

/-- The rational end points of the angle `aπ/b`. -/
lemma angle_ends (a b : ℕ) (hb : 0 < b) :
    ((a * PLO : ℕ) : ℝ) / ((b * 2 ^ PIS : ℕ) : ℝ) = (a / b) * ((PLO : ℝ) / 2 ^ PIS) ∧
      ((a * PHI : ℕ) : ℝ) / ((b * 2 ^ PIS : ℕ) : ℝ) = (a / b) * ((PHI : ℝ) / 2 ^ PIS) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  constructor <;> (push_cast; field_simp)

lemma cosQ_encl {a b : ℕ} (hab : 4 * a ≤ b) (hb : 0 < b) : Encl PR (cosQ a b) (cos (a * π / b)) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd : 0 < b * 2 ^ PIS := by positivity
  have hab' : (a : ℝ) / b ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hb' (by norm_num)]; exact_mod_cast (by omega : a * 4 ≤ 1 * b)
  have ha0 : (0 : ℝ) ≤ a / b := by positivity
  obtain ⟨eL, eH⟩ := angle_ends a b hb
  set xl : ℝ := (a / b) * ((PLO : ℝ) / 2 ^ PIS)
  set xh : ℝ := (a / b) * ((PHI : ℝ) / 2 ^ PIS)
  have hx : (a : ℝ) * π / b = (a / b) * π := by ring
  have h1 : xl ≤ a * π / b := by rw [hx]; exact mul_le_mul_of_nonneg_left PLO_le_pi ha0
  have h2 : a * π / b ≤ xh := by rw [hx]; exact mul_le_mul_of_nonneg_left pi_le_PHI ha0
  have hxl0 : 0 ≤ xl := mul_nonneg ha0 PLO_div_nonneg
  have hxh : xh ≤ 4 / 5 := by
    calc xh ≤ (1 / 4) * (16 / 5) := mul_le_mul hab' PHI_div_le (by positivity) (by norm_num)
      _ = 4 / 5 := by norm_num
  have hpi : (4 / 5 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hx0 : 0 ≤ (a : ℝ) * π / b := by positivity
  obtain ⟨hs1, hs1v⟩ := cosSeries_spec (a * PHI) (b * 2 ^ PIS) hd
  obtain ⟨hs2, hs2v⟩ := cosSeries_spec (a * PLO) (b * 2 ^ PIS) hd
  rw [eH] at hs1v
  rw [eL] at hs2v
  unfold cosQ
  constructor
  · refine rnd_fst_le hs1 ?_
    rw [hs1v]
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx0 (hxh.trans hpi) h2
    have hr := cos_rem_small (x := xh) (by rw [abs_of_nonneg (hxl0.trans (h1.trans h2))]; exact hxh)
    rw [abs_le] at hr
    linarith [hr.1]
  · refine le_rnd_snd hs2 ?_
    rw [hs2v]
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hxl0 ((h2.trans hxh).trans hpi) h1
    have hr := cos_rem_small (x := xl) (by rw [abs_of_nonneg hxl0]; linarith)
    rw [abs_le] at hr
    linarith [hr.2]

lemma sinQ_encl {a b : ℕ} (hab : 4 * a ≤ b) (hb : 0 < b) : Encl PR (sinQ a b) (sin (a * π / b)) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd : 0 < b * 2 ^ PIS := by positivity
  have hab' : (a : ℝ) / b ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hb' (by norm_num)]; exact_mod_cast (by omega : a * 4 ≤ 1 * b)
  have ha0 : (0 : ℝ) ≤ a / b := by positivity
  obtain ⟨eL, eH⟩ := angle_ends a b hb
  set xl : ℝ := (a / b) * ((PLO : ℝ) / 2 ^ PIS)
  set xh : ℝ := (a / b) * ((PHI : ℝ) / 2 ^ PIS)
  have hx : (a : ℝ) * π / b = (a / b) * π := by ring
  have h1 : xl ≤ a * π / b := by rw [hx]; exact mul_le_mul_of_nonneg_left PLO_le_pi ha0
  have h2 : a * π / b ≤ xh := by rw [hx]; exact mul_le_mul_of_nonneg_left pi_le_PHI ha0
  have hxl0 : 0 ≤ xl := mul_nonneg ha0 PLO_div_nonneg
  have hxh : xh ≤ 4 / 5 := by
    calc xh ≤ (1 / 4) * (16 / 5) := mul_le_mul hab' PHI_div_le (by positivity) (by norm_num)
      _ = 4 / 5 := by norm_num
  have hpi : (4 / 5 : ℝ) ≤ π / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨hs1, hs1v⟩ := sinSeries_spec (a * PLO) (b * 2 ^ PIS) hd
  obtain ⟨hs2, hs2v⟩ := sinSeries_spec (a * PHI) (b * 2 ^ PIS) hd
  rw [eL] at hs1v
  rw [eH] at hs2v
  have hneg : -(π / 2) ≤ xl := by linarith [Real.pi_pos]
  unfold sinQ
  constructor
  · refine rnd_fst_le hs1 ?_
    rw [hs1v]
    have hc := Real.sin_le_sin_of_le_of_le_pi_div_two hneg (by linarith) h1
    have hr := sin_rem_small (x := xl) (by rw [abs_of_nonneg hxl0]; linarith)
    rw [abs_le] at hr
    linarith [hr.2]
  · refine le_rnd_snd hs2 ?_
    rw [hs2v]
    have hc := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hxh.trans hpi) h2
    have hr := sin_rem_small (x := xh) (by rw [abs_of_nonneg (hxl0.trans (h1.trans h2))]; exact hxh)
    rw [abs_le] at hr
    linarith [hr.1]

/-! ## Reductions -/

lemma Encl.congr {s : ℕ} {a : ℤ × ℤ} {x y : ℝ} (h : Encl s a x) (e : x = y) : Encl s a y := e ▸ h

lemma cosRed_encl {a b : ℕ} (hab : a ≤ b) (hb : 0 < b) : Encl PR (cosRed a b) (cos (a * π / b)) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  unfold cosRed
  split_ifs with h1 h2 h3
  · exact cosQ_encl h1 hb
  · refine (sinQ_encl (by omega) (by omega)).congr ?_
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    field_simp
  · refine (ineg_encl (sinQ_encl (by omega) (by omega))).congr ?_
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [show ((2 : ℝ) * a - b) * π / (2 * b) = a * π / b - π / 2 by field_simp, Real.sin_sub_pi_div_two,
      neg_neg]
  · refine (ineg_encl (cosQ_encl (by omega) hb)).congr ?_
    rw [Nat.cast_sub hab]
    rw [show ((b : ℝ) - a) * π / b = π - a * π / b by field_simp, Real.cos_pi_sub, neg_neg]

lemma cosPi_encl (a : ℤ) {b : ℕ} (hb : 0 < b) : Encl PR (cosPi a b) (cos (a * π / b)) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  unfold cosPi
  simp only
  set a1 := a.natAbs % (2 * b) with ha1
  have ha1lt : a1 < 2 * b := Nat.mod_lt _ (by omega)
  -- cos(aπ/b) = cos(a1 π/b)
  have hq := Nat.div_add_mod a.natAbs (2 * b)
  set q := a.natAbs / (2 * b) with hqdef
  have hcast : (a.natAbs : ℝ) = 2 * b * (q : ℝ) + a1 := by
    have : a.natAbs = 2 * b * q + a1 := hq.symm
    exact_mod_cast this
  have e1 : cos (a * π / b) = cos (a1 * π / b) := by
    rw [← Real.cos_abs, show |(a : ℝ) * π / b| = (a.natAbs : ℝ) * π / b by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hb', Nat.cast_natAbs, Int.cast_abs]]
    rw [hcast, show (2 * (b : ℝ) * (q : ℝ) + a1) * π / b = a1 * π / b + ((q : ℤ) : ℝ) * (2 * π) by
      rw [Int.cast_natCast]; field_simp; ring]
    exact Real.cos_add_int_mul_two_pi _ _
  split_ifs with h
  · refine (cosRed_encl (by omega) hb).congr ?_
    rw [e1, Nat.cast_sub ha1lt.le]
    push_cast
    rw [show (2 * (b : ℝ) - a1) * π / b = 2 * π - a1 * π / b by field_simp, Real.cos_two_pi_sub]
  · exact (cosRed_encl (by omega) hb).congr e1.symm

lemma sinPi_encl (a : ℤ) {b : ℕ} (hb : 0 < b) : Encl PR (sinPi a b) (sin (a * π / b)) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  refine (cosPi_encl (2 * a - Int.ofNat b) (by omega : 0 < 2 * b)).congr ?_
  simp only [Int.ofNat_eq_natCast]
  push_cast
  rw [show (2 * (a : ℝ) - b) * π / (2 * b) = a * π / b - π / 2 by field_simp, Real.cos_sub_pi_div_two]

end LebTrig.Sound
