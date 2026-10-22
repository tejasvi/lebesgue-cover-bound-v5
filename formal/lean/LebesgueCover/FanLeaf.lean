import LebesgueCover.Sound
import LebesgueCover.Fan

/-!
# The fan lemma at a leaf

A passing leaf gives, at every placement of its box, an area bound for every convex set that contains the fan centre
and the placed witnesses. The positive fan rows give positive turns along the straight homotopy from the placement
`y = 0` (box centre) to the placement; the winding certificate gives total turning `< 4π` at `y = 0`; so the turning
is exactly `2π` at the placement and the fan lemma applies. The shoelace identity identifies the fan area.
-/

open Finset MeasureTheory

namespace LebesgueCover.Cert

/-- A point of `ℝ × ℝ` as a complex number. -/
def toC (P : ℝ × ℝ) : ℂ := ⟨P.1, P.2⟩

lemma detC_toC (P Q : ℝ × ℝ) : detC (toC P) (toC Q) = det2R P Q := rfl
lemma dotC_toC (P Q : ℝ × ℝ) : dotC (toC P) (toC Q) = dot2R P Q := rfl
lemma toC_subR (P Q : ℝ × ℝ) : toC (subR P Q) = toC P - toC Q := by
  apply Complex.ext <;> simp [toC, subR]

/-! ## Cyclic pairs by index -/

/-- The `j`-th witness. -/
def wAt (W : List Wit) (j : ℕ) : Wit := W.getD j ⟨0, (0, 0)⟩

lemma cycPairs_eq (W : List Wit) :
    cycPairs W = (List.range W.length).map fun j => (wAt W j, wAt W (nxt W.length j)) := by
  cases W with
  | nil => rfl
  | cons a t =>
    apply List.ext_getElem
    · simp [cycPairs]
    · intro j h1 h2
      have hj : j < t.length + 1 := by simpa using h2
      simp only [cycPairs, List.getElem_zip, List.getElem_map, List.getElem_range, wAt, nxt, List.length_cons]
      rw [List.getD_eq_getElem _ _ hj]
      rcases Nat.lt_or_ge j t.length with hjt | hjt
      · rw [Nat.mod_eq_of_lt (by omega : j + 1 < t.length + 1), List.getD_eq_getElem _ _ (by simpa using hjt),
          List.getElem_append_left hjt]
        simp
      · have hjt' : j = t.length := by omega
        subst hjt'
        simp

lemma list_range_map_sum {β : Type*} [AddCommMonoid β] (n : ℕ) (h : ℕ → β) :
    ((List.range n).map h).sum = ∑ j ∈ range n, h j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma cycPairs_sum {β : Type*} [AddCommMonoid β] (W : List Wit) (f : Wit × Wit → β) :
    ((cycPairs W).map f).sum = ∑ j ∈ range W.length, f (wAt W j, wAt W (nxt W.length j)) := by
  rw [cycPairs_eq, List.map_map, list_range_map_sum]; rfl

lemma mem_cycPairs_idx (W : List Wit) {j : ℕ} (hj : j < W.length) :
    (wAt W j, wAt W (nxt W.length j)) ∈ cycPairs W := by
  rw [cycPairs_eq]; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

lemma wAt_mem (W : List Wit) {j : ℕ} (hj : j < W.length) : wAt W j ∈ W := by
  simp only [wAt]; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

/-! ## Shoelace -/

lemma sum_nxt {β : Type*} [AddCommMonoid β] (m : ℕ) (g : ℕ → β) :
    ∑ j ∈ range m, g (nxt m j) = ∑ j ∈ range m, g j := by
  rcases m with _ | m
  · simp
  · rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun j => g j)]
    have hlast : nxt (m + 1) m = 0 := by simp [nxt]
    rw [hlast]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j < m := Finset.mem_range.mp hj
    simp [nxt, Nat.mod_eq_of_lt (by omega : j + 1 < m + 1)]

/-- The fan area does not depend on the centre. -/
lemma shoelace (m : ℕ) (x : ℕ → ℝ × ℝ) (z : ℝ × ℝ) :
    ∑ j ∈ range m, det2R (subR (x j) z) (subR (x (nxt m j)) z) = ∑ j ∈ range m, det2R (x j) (x (nxt m j)) := by
  have e : ∀ j, det2R (subR (x j) z) (subR (x (nxt m j)) z) =
      det2R (x j) (x (nxt m j)) - det2R (x j) z + det2R (x (nxt m j)) z := fun j => by
    simp only [det2R, subR]; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hs : ∑ j ∈ range m, det2R (x (nxt m j)) z = ∑ j ∈ range m, det2R (x j) z :=
    sum_nxt m (fun j => det2R (x j) z)
  linarith

/-! ## The y-box contains `0` and is star-shaped about it -/

lemma yCentre_cases (bb : ℕ → BodyBox) (v : ℕ) : yCentre bb v = 0 ∨ yCentre bb v = -yHalf bb v := by
  unfold yCentre yHalf
  split_ifs with h
  · right; simp [h]; ring
  · left; rfl

lemma box_smul {n : ℕ} {y y0 w : ℕ → ℝ} (hy : ∀ v ∈ range n, |y v - y0 v| ≤ w v)
    (h0 : ∀ v, y0 v = 0 ∨ y0 v = -w v) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ v ∈ range n, |t * y v - y0 v| ≤ w v := by
  intro v hv
  have hw : 0 ≤ w v := (abs_nonneg _).trans (hy v hv)
  have h1 := hy v hv
  obtain ⟨ht0, ht1⟩ := ht
  have hzero : |0 - y0 v| ≤ w v := by rcases h0 v with h | h <;> simp [h, abs_of_nonneg hw, hw]
  rw [abs_le] at h1 hzero ⊢
  constructor <;> nlinarith [h1.1, h1.2, hzero.1, hzero.2]

lemma toC_lin_smul (n : ℕ) (P0 : ℝ × ℝ) (L : ℕ → ℝ × ℝ) (y : ℕ → ℝ) (t : ℝ) :
    toC (lin n P0 L (fun v => t * y v)) = ((1 - t : ℝ) : ℂ) * toC P0 + (t : ℂ) * toC (lin n P0 L y) := by
  have e1 : ∑ v ∈ range n, t * y v * (L v).1 = t * ∑ v ∈ range n, y v * (L v).1 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
  have e2 : ∑ v ∈ range n, t * y v * (L v).2 = t * ∑ v ∈ range n, y v * (L v).2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
  apply Complex.ext
  · simp only [toC, lin, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, e1]; ring
  · simp only [toC, lin, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, e2]; ring

/-! ## The winding certificate -/

lemma cast_angleUB (P Q : ℚ × ℚ) :
    ((angleUB P Q : ℚ) : ℝ) = angleUBR ((dot2 P Q : ℚ) : ℝ) ((det2 P Q : ℚ) : ℝ) := by
  unfold angleUB angleUBR
  by_cases h : 0 < dot2 P Q
  · rw [if_pos h, if_pos (by exact_mod_cast h)]; push_cast; ring_nf
  · rw [if_neg h, if_neg (by exact_mod_cast h)]; push_cast; ring_nf

/-- `P − z` over `ℚ`. -/
def subQ (P z : ℚ × ℚ) : ℚ × ℚ := (P.1 - z.1, P.2 - z.2)

lemma windOK_sum {bb : ℕ → BodyBox} {z : ℚ × ℚ} {W : List Wit} (h : windOK bb z W = true) :
    ∑ j ∈ range W.length, angleUB (subQ (witX0 bb (wAt W j)) z) (subQ (witX0 bb (wAt W (nxt W.length j))) z)
      < 4 * (31415 / 10000) := by
  simp only [windOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 := h.2
  rw [List.map_map, cycPairs_sum] at h2
  exact h2

/-! ## The leaf area bound -/

/-- **Fan bound.** If the fan checks pass on a box, then at every placement `p` of the box the fan area is positive
and at most the area of every convex `K ⊆ ℂ` that contains the fan centre `z` and the placed witnesses. -/
theorem fan_area_bound {ns : List ℕ} {vt : VertTable} {lo hi : ℕ → ℚ} {W : List Wit} {z : ℚ × ℚ} {p : ℕ → ℝ}
    (F : FanFacts ns vt lo hi W z p)
    {K : Set ℂ} (hK : Convex ℝ K) (hz : toC (castP z) ∈ K) (hx : ∀ w ∈ W, toC (witPos p w) ∈ K) :
    0 < fanAreaR p W ∧ ENNReal.ofReal (fanAreaR p W) ≤ volume K := by
  have hm : 0 < W.length := by have := F.len; omega
  obtain ⟨c, hc_def⟩ : ∃ c : ℕ → ℂ, c = fun j => toC (subR (witPos p (wAt W j)) (castP z)) := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℕ → ℂ,
      b = fun j => toC (subR (castP (witX0 (bodyBox lo hi) (wAt W j))) (castP z)) := ⟨_, rfl⟩
  have hnx : ∀ j, nxt W.length j < W.length := fun j => Nat.mod_lt _ hm
  -- the vertices along the homotopy are the linearized positions at `t • y(p)`
  have hlinj : ∀ j < W.length, ∀ t : ℝ, homC b c t j =
      toC (lin (4 * ns.length - 2) (subR (castP (witX0 (bodyBox lo hi) (wAt W j))) (castP z))
        (fun v => castP (witL (bodyBox lo hi) (wAt W j) v)) (fun v => t * yAt lo hi p v)) := by
    intro j hj t
    rw [toC_lin_smul, hb_def, hc_def]
    simp only [homC]
    rw [F.lin_eq _ (wAt_mem W hj), lin_sub]
  have hbox_t : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ range (4 * ns.length - 2),
      |t * yAt lo hi p v - (yCentre (bodyBox lo hi) v : ℝ)| ≤ (yHalf (bodyBox lo hi) v : ℝ) := by
    intro t ht
    refine box_smul F.box (fun v => ?_) ht
    rcases yCentre_cases (bodyBox lo hi) v with e | e
    · left; rw [e]; simp
    · right; rw [e]; simp
  have hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j < W.length,
      0 < detC (homC b c t j) (homC b c t (nxt W.length j)) := by
    intro t ht j hj
    rw [hlinj j hj t, hlinj _ (hnx j) t, detC_toC]
    exact fanRow_sound_y lo hi z (wAt W j) (wAt W (nxt W.length j)) (fun v => t * yAt lo hi p v) (hbox_t t ht)
      (F.rows (wAt W j, wAt W (nxt W.length j)) (mem_cycPairs_idx W hj))
  -- winding at the centre placement
  have hb0 : ∀ j < W.length, 0 < detC (b j) (b (nxt W.length j)) := fun j hj => by
    have := hdet 0 ⟨le_rfl, zero_le_one⟩ j hj
    rwa [homC_zero] at this
  have h4 : turnSum b W.length < 4 * Real.pi := by
    have hsum := windOK_sum F.wind
    have hsumR : ∑ j ∈ range W.length, ((angleUB (subQ (witX0 (bodyBox lo hi) (wAt W j)) z)
        (subQ (witX0 (bodyBox lo hi) (wAt W (nxt W.length j))) z) : ℚ) : ℝ) < 4 * (31415 / 10000 : ℝ) := by
      have := (Rat.cast_lt (K := ℝ)).mpr hsum
      rw [Rat.cast_sum] at this
      convert this using 1
      norm_num
    have hpi := Real.pi_gt_d4
    calc turnSum b W.length = ∑ j ∈ range W.length, Complex.arg (b (nxt W.length j) / b j) := rfl
      _ ≤ ∑ j ∈ range W.length, angleUBR (dotC (b j) (b (nxt W.length j))) (detC (b j) (b (nxt W.length j))) :=
          Finset.sum_le_sum fun j hj => arg_div_le_angleUBR (ne_zero_of_detC_pos (hb0 j (mem_range.mp hj)))
            (hb0 j (mem_range.mp hj))
      _ = ∑ j ∈ range W.length, ((angleUB (subQ (witX0 (bodyBox lo hi) (wAt W j)) z)
            (subQ (witX0 (bodyBox lo hi) (wAt W (nxt W.length j))) z) : ℚ) : ℝ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [cast_angleUB, cast_dot2, cast_det2, hb_def]
          simp only [dotC_toC, detC_toC, subQ, castP_sub]
      _ < 4 * (31415 / 10000 : ℝ) := hsumR
      _ < 4 * Real.pi := by norm_num at hpi ⊢; linarith
  -- winding at the placement, and the fan lemma
  have hturn := wind_homotopy hm b c hdet h4
  have hwind' : cum c W.length W.length = cum c W.length 0 + 2 * Real.pi := by rw [cum_m_eq, hturn]
  have hc_det : ∀ j < W.length, 0 < detC (c j) (c (nxt W.length j)) := fun j hj => by
    have := hdet 1 ⟨zero_le_one, le_rfl⟩ j hj
    rwa [homC_one] at this
  have hfan := fan_area_le hK hm hz (a := c)
    (fun j hj => by
      have e : toC (castP z) + c j = toC (witPos p (wAt W j)) := by rw [hc_def]; simp only [toC_subR]; ring
      rw [e]; exact hx _ (wAt_mem W hj))
    (fun j hj => ne_zero_of_detC_pos (hc_det j hj)) hc_det hwind'
  have harea_eq : ∑ j ∈ range W.length, detC (c j) (c (nxt W.length j)) / 2 = fanAreaR p W := by
    unfold fanAreaR
    simp only [cycPairs_sum]
    rw [← Finset.sum_div, ← Finset.sum_div, hc_def]
    congr 1
    simp only [detC_toC]
    exact shoelace W.length (fun j => witPos p (wAt W j)) (castP z)
  rw [harea_eq] at hfan
  have hpos : 0 < fanAreaR p W := by
    rw [← harea_eq]
    exact Finset.sum_pos (fun j hj => div_pos (hc_det j (mem_range.mp hj)) two_pos) ⟨0, mem_range.mpr hm⟩
  exact ⟨hpos, hfan⟩

/-- **Fan bound at a leaf.** If a leaf passes, then at every placement `p` of its box, every convex `K ⊆ ℂ` that
contains the fan centre `z` and the placed witnesses has area `> τ`. -/
theorem leaf_fan {ns : List ℕ} {vt : VertTable} {τ : ℚ} {lo hi : ℕ → ℚ} {W : List Wit} {z : ℚ × ℚ}
    {β σ : ℕ → ℚ} (h : leafOK ns vt τ lo hi W z β σ = true) (p : ℕ → ℝ)
    (hp : ∀ a, a < 3 * ns.length - 1 → (lo a : ℝ) ≤ p a ∧ p a ≤ hi a)
    {K : Set ℂ} (hK : Convex ℝ K) (hz : toC (castP z) ∈ K) (hx : ∀ w ∈ W, toC (witPos p w) ∈ K) :
    ENNReal.ofReal τ < volume K := by
  have F := leafOK_sound h p hp
  obtain ⟨hpos, hfan⟩ := fan_area_bound F.toFanFacts hK hz hx
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hpos).mpr F.area) hfan

lemma lsum_le {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

lemma lsum_add {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma lsum_nonneg_mul_le {α : Type*} (l : List α) (c f : α → ℝ) (t : ℝ) (hc : ∀ x ∈ l, 0 ≤ c x)
    (hf : ∀ x ∈ l, f x ≤ t) : (l.map fun x => c x * f x).sum ≤ (l.map c).sum * t := by
  rw [← List.sum_map_mul_right]
  exact lsum_le l _ _ fun x hx => mul_le_mul_of_nonneg_left (hf x hx) (hc x hx)

/-- **Combination bound at a leaf** (Lemma 3.8 of the paper). If a combination leaf passes, then at every
placement `p` of its box, every convex `K ⊆ ℂ` that contains the centres and the placed witnesses of all its fans has
area `> τ`. -/
theorem comb_fan {ns : List ℕ} {vt : VertTable} {τ : ℚ} {lo hi : ℕ → ℚ}
    {fans : List (List Wit × (ℚ × ℚ) × (ℕ → ℚ) × (ℕ → ℚ) × ℚ)}
    (h : combOK ns vt τ lo hi fans = true) (p : ℕ → ℝ)
    (hp : ∀ a, a < 3 * ns.length - 1 → (lo a : ℝ) ≤ p a ∧ p a ≤ hi a)
    {K : Set ℂ} (hK : Convex ℝ K) (hz : ∀ F ∈ fans, toC (castP F.2.1) ∈ K)
    (hx : ∀ F ∈ fans, ∀ w ∈ F.1, toC (witPos p w) ∈ K) :
    ENNReal.ofReal τ < volume K := by
  simp only [combOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hsok, hk⟩, hfans⟩, hS⟩, hbound⟩ := h
  set k := ns.length with hkdef
  set n := 4 * k - 2 with hn
  set bb := bodyBox lo hi with hbb
  have hs : ∀ i, 2 ≤ i → i ≤ k → (bb i).sOK = true := fun i _ hi => hsok i (by omega)
  -- per fan: the facts, the area bound and the affine minorant
  have hfan : ∀ F ∈ fans, 0 ≤ F.2.2.2.2 ∧ 0 < fanAreaR p F.1 ∧ ENNReal.ofReal (fanAreaR p F.1) ≤ volume K ∧
      ((fanA n bb (fanQuad bb F.1 F.2.2.1) F.2.2.2.1 : ℚ) : ℝ) +
        ∑ a ∈ range n, ((fanG n bb (fanQuad bb F.1 F.2.2.1) a : ℚ) : ℝ) * (yAt lo hi p a - (yCentre bb a : ℝ))
        ≤ fanAreaR p F.1 := by
    intro F hF
    obtain ⟨hl, hok⟩ := hfans F hF
    obtain ⟨FF, hT⟩ := fanOK_sound hok hk hs p hp
    obtain ⟨hpos, hle⟩ := fan_area_bound FF hK (hz F hF) (hx F hF)
    exact ⟨by exact_mod_cast hl, hpos, hle, hT⟩
  by_contra hcon
  push Not at hcon
  -- every fan area is at most τ
  have hτ : ∀ F ∈ fans, fanAreaR p F.1 ≤ τ := by
    intro F hF
    obtain ⟨-, hpos, hle, -⟩ := hfan F hF
    by_contra hlt; push Not at hlt
    have := (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hlt
    exact absurd (lt_of_lt_of_le this (hle.trans hcon)) (lt_irrefl _)
  -- the weighted sum of the fan areas
  set Δ : ℕ → ℝ := fun a => yAt lo hi p a - (yCentre bb a : ℝ) with hΔ
  have hup : (fans.map fun F => (F.2.2.2.2 : ℝ) * fanAreaR p F.1).sum ≤ (fans.map fun F => (F.2.2.2.2 : ℝ)).sum * τ :=
    lsum_nonneg_mul_le fans _ _ _ (fun F hF => (hfan F hF).1 |> fun h => by exact_mod_cast h) hτ
  have hlow : (fans.map fun F => (F.2.2.2.2 : ℝ) * ((fanA n bb (fanQuad bb F.1 F.2.2.1) F.2.2.2.1 : ℚ) : ℝ)).sum +
      ∑ a ∈ range n, (fans.map fun F => (F.2.2.2.2 : ℝ) *
        ((fanG n bb (fanQuad bb F.1 F.2.2.1) a : ℚ) : ℝ)).sum * Δ a ≤
      (fans.map fun F => (F.2.2.2.2 : ℝ) * fanAreaR p F.1).sum := by
    have e : (fans.map fun F => (F.2.2.2.2 : ℝ) * ((fanA n bb (fanQuad bb F.1 F.2.2.1) F.2.2.2.1 : ℚ) : ℝ)).sum +
        ∑ a ∈ range n, (fans.map fun F => (F.2.2.2.2 : ℝ) *
          ((fanG n bb (fanQuad bb F.1 F.2.2.1) a : ℚ) : ℝ)).sum * Δ a =
        (fans.map fun F => (F.2.2.2.2 : ℝ) * (((fanA n bb (fanQuad bb F.1 F.2.2.1) F.2.2.2.1 : ℚ) : ℝ) +
          ∑ a ∈ range n, ((fanG n bb (fanQuad bb F.1 F.2.2.1) a : ℚ) : ℝ) * Δ a)).sum := by
      have e1 : ∀ F : List Wit × (ℚ × ℚ) × (ℕ → ℚ) × (ℕ → ℚ) × ℚ,
          (F.2.2.2.2 : ℝ) * (((fanA n bb (fanQuad bb F.1 F.2.2.1) F.2.2.2.1 : ℚ) : ℝ) +
            ∑ a ∈ range n, ((fanG n bb (fanQuad bb F.1 F.2.2.1) a : ℚ) : ℝ) * Δ a) =
          (F.2.2.2.2 : ℝ) * ((fanA n bb (fanQuad bb F.1 F.2.2.1) F.2.2.2.1 : ℚ) : ℝ) +
            ∑ a ∈ range n, (F.2.2.2.2 : ℝ) * ((fanG n bb (fanQuad bb F.1 F.2.2.1) a : ℚ) : ℝ) * Δ a := by
        intro F; rw [mul_add, Finset.mul_sum]; congr 1; exact Finset.sum_congr rfl fun a _ => by ring
      simp_rw [e1]
      rw [lsum_add, list_sum_finset_sum]
      congr 1
      exact Finset.sum_congr rfl fun a _ => by rw [List.sum_map_mul_right]
    rw [e]
    exact lsum_le fans _ _ fun F hF => mul_le_mul_of_nonneg_left (hfan F hF).2.2.2 (by exact_mod_cast (hfan F hF).1)
  -- the certified bound, cast to ℝ
  have hb : (τ : ℝ) * (fans.map fun F => (F.2.2.2.2 : ℝ)).sum <
      (fans.map fun F => (F.2.2.2.2 : ℝ) * ((fanA n bb (fanQuad bb F.1 F.2.2.1) F.2.2.2.1 : ℚ) : ℝ)).sum -
        ∑ a ∈ range n, |(fans.map fun F => (F.2.2.2.2 : ℝ) *
          ((fanG n bb (fanQuad bb F.1 F.2.2.1) a : ℚ) : ℝ)).sum| * (yHalf bb a : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr hbound
    push_cast [Rat.cast_list_sum, List.map_map] at this
    convert this using 2 <;> simp [Function.comp_def]
  -- the linear term is at least `−Σ |·| w`
  have hlin : -∑ a ∈ range n, |(fans.map fun F => (F.2.2.2.2 : ℝ) *
      ((fanG n bb (fanQuad bb F.1 F.2.2.1) a : ℚ) : ℝ)).sum| * (yHalf bb a : ℝ) ≤
      ∑ a ∈ range n, (fans.map fun F => (F.2.2.2.2 : ℝ) *
        ((fanG n bb (fanQuad bb F.1 F.2.2.1) a : ℚ) : ℝ)).sum * Δ a := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun a ha => ?_
    have hy := yAt_mem_box lo hi p hs hp a ha
    set c := (fans.map fun F => (F.2.2.2.2 : ℝ) * ((fanG n bb (fanQuad bb F.1 F.2.2.1) a : ℚ) : ℝ)).sum
    have h2 : -(|c| * |Δ a|) ≤ c * Δ a := by rw [← abs_mul]; exact neg_abs_le _
    have h3 := mul_le_mul_of_nonneg_left hy (abs_nonneg c)
    simp only [hΔ] at h2 ⊢
    linarith
  have hSR : (0 : ℝ) < (fans.map fun F => (F.2.2.2.2 : ℝ)).sum := by
    have := (Rat.cast_lt (K := ℝ)).mpr hS
    push_cast [Rat.cast_list_sum, List.map_map] at this
    simpa [Function.comp_def] using this
  nlinarith

end LebesgueCover.Cert
