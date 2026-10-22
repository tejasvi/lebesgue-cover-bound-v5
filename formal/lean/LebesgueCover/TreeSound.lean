import LebesgueCover.FastBridge
import LebesgueCover.FanLeaf
import LebFast.Tree
import LebesgueCover.Defs

/-!
# Soundness of certificate trees

`GoodBox ns τ lo hi`: at every placement of the box, every convex set of the complex plane that contains the disk
and the placed Reuleaux bodies has area `> τ`. A passing leaf (single fan or combination) gives `GoodBox` for its box
(given a correct vertex table), and a passing tree gives it for its cell.
-/

open MeasureTheory Finset

namespace LebesgueCover.Cert

/-- The disk of diameter `1` in `ℂ`. -/
def diskC : Set ℂ := Metric.closedBall 0 (1 / 2)

/-- The vertex `V_{n,l} = R_n e^{2πil/n}`. -/
noncomputable def vertC (n l : ℕ) : ℂ :=
  ⟨circR n * Real.cos (2 * Real.pi * l / n), circR n * Real.sin (2 * Real.pi * l / n)⟩

/-- The Reuleaux polygon `B_n = ⋂_{l<n} D(V_{n,l}, 1)` in `ℂ`. -/
def reuleauxC (n : ℕ) : Set ℂ := ⋂ l ∈ Finset.range n, Metric.closedBall (vertC n l) 1

/-- Body `i` at the placement `p`: `q ↦ u q + t` (`u = 1, t = 0` for the disk; `u = 1` for body 1). -/
noncomputable def placeC (p : ℕ → ℝ) (i : ℕ) (q : ℂ) : ℂ := toC (rotAt p i) * q + toC (transAt p i)

/-- A correct vertex table. -/
def VertTableOK (ns : List ℕ) (V : ℕ → ℕ → ℚ × ℚ) (ν : ℚ) : Prop :=
  0 ≤ ν ∧ ν ≤ 1 ∧ ∀ n ∈ ns, ∀ l < n, ‖toC (castP (V n l)) - vertC n l‖ ≤ ν

/-- The conclusion at a box. -/
def GoodBox (ns : List ℕ) (τ : ℚ) (lo hi : ℕ → ℚ) : Prop :=
  ∀ p : ℕ → ℝ, (∀ a, a < 3 * ns.length - 1 → (lo a : ℝ) ≤ p a ∧ p a ≤ hi a) →
    ∀ K : Set ℂ, Convex ℝ K → diskC ⊆ K →
      (∀ i, 1 ≤ i → i ≤ ns.length → ∀ q ∈ reuleauxC (ns.getD (i - 1) 0), placeC p i q ∈ K) →
        ENNReal.ofReal τ < volume K

lemma toC_witPos (p : ℕ → ℝ) (w : Wit) : toC (witPos p w) = placeC p w.body (toC (castP w.pt)) := by
  apply Complex.ext <;> simp [toC, witPos, placeC, rot2R, Complex.mul_re, Complex.mul_im] <;> ring

lemma placeC_zero (p : ℕ → ℝ) (q : ℂ) : placeC p 0 q = q := by
  apply Complex.ext <;> simp [placeC, rotAt, transAt, toC, Complex.mul_re, Complex.mul_im]

lemma norm_toC (P : ℝ × ℝ) : ‖toC P‖ = Real.sqrt (P.1 ^ 2 + P.2 ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]; simp [toC, sq]

/-- **Witness membership.** A witness that passes `memOK` lies in its body. -/
lemma mem_of_memOK {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν : ℚ} (hV : VertTableOK ns V ν) {w : Wit}
    (hb : w.body ≤ ns.length) (h : memOK ns ⟨V, ν⟩ w = true) :
    (w.body = 0 ∧ toC (castP w.pt) ∈ diskC) ∨
      (1 ≤ w.body ∧ toC (castP w.pt) ∈ reuleauxC (ns.getD (w.body - 1) 0)) := by
  unfold memOK at h
  split_ifs at h with h0
  · left
    refine ⟨h0, ?_⟩
    simp only [decide_eq_true_eq] at h
    rw [diskC, Metric.mem_closedBall, dist_zero_right, norm_toC]
    have h' : ((w.pt.1 : ℝ)) ^ 2 + (w.pt.2 : ℝ) ^ 2 ≤ 1 / 4 := by
      have := (Rat.cast_le (K := ℝ)).mpr h; push_cast [dot2] at this; nlinarith
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by simpa [castP] using h')
  · right
    refine ⟨by omega, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨hn, hl⟩ := h
    set n := ns.getD (w.body - 1) 0 with hn_def
    have hnmem : n ∈ ns := by
      rw [hn_def, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    simp only [reuleauxC, Set.mem_iInter, Metric.mem_closedBall]
    intro l hl'
    rw [Finset.mem_range] at hl'
    have h1 := hl l hl'
    have hd : ‖toC (castP w.pt) - toC (castP (V n l))‖ ≤ 1 - ν := by
      have e : toC (castP w.pt) - toC (castP (V n l)) = toC (castP (w.pt.1 - (V n l).1, w.pt.2 - (V n l).2)) := by
        apply Complex.ext <;> simp [toC, castP]
      rw [e, norm_toC]
      have h1' : (((w.pt.1 - (V n l).1 : ℚ) : ℝ)) ^ 2 + ((w.pt.2 - (V n l).2 : ℚ) : ℝ) ^ 2 ≤ ((1 - ν : ℚ) : ℝ) ^ 2 := by
        have := (Rat.cast_le (K := ℝ)).mpr h1; push_cast [dot2] at this ⊢; nlinarith
      have hν : (0 : ℝ) ≤ 1 - ν := by have := hV.2.1; exact_mod_cast (by linarith : (0 : ℚ) ≤ 1 - ν)
      calc Real.sqrt (_) ≤ Real.sqrt (((1 - ν : ℚ) : ℝ) ^ 2) := Real.sqrt_le_sqrt (by simpa [castP] using h1')
        _ = 1 - ν := by rw [Real.sqrt_sq (by exact_mod_cast hν)]; push_cast; ring
    have hv := hV.2.2 n hnmem l hl'
    rw [dist_eq_norm]
    calc ‖toC (castP w.pt) - vertC n l‖
        = ‖(toC (castP w.pt) - toC (castP (V n l))) + (toC (castP (V n l)) - vertC n l)‖ := by ring_nf
      _ ≤ ‖toC (castP w.pt) - toC (castP (V n l))‖ + ‖toC (castP (V n l)) - vertC n l‖ := norm_add_le _ _
      _ ≤ (1 - ν) + ν := add_le_add hd hv
      _ = 1 := by ring

lemma zmem_disk {z : ℚ × ℚ} (h : dot2 z z < 1 / 4) : toC (castP z) ∈ diskC := by
  rw [diskC, Metric.mem_closedBall, dist_zero_right, norm_toC]
  have h' : ((z.1 : ℝ)) ^ 2 + (z.2 : ℝ) ^ 2 ≤ 1 / 4 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h; push_cast [dot2] at this; nlinarith
  rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by simpa [castP] using h')

lemma wit_mem_K {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν : ℚ} (hV : VertTableOK ns V ν) {p : ℕ → ℝ} {K : Set ℂ}
    (hD : diskC ⊆ K) (hB : ∀ i, 1 ≤ i → i ≤ ns.length → ∀ q ∈ reuleauxC (ns.getD (i - 1) 0), placeC p i q ∈ K)
    {w : Wit} (hb : w.body ≤ ns.length) (hm : memOK ns ⟨V, ν⟩ w = true) : toC (witPos p w) ∈ K := by
  rw [toC_witPos]
  rcases mem_of_memOK hV hb hm with ⟨h0, hq⟩ | ⟨h1, hq⟩
  · rw [h0, placeC_zero]; exact hD hq
  · exact hB w.body h1 hb _ hq

/-- **A passing single-fan leaf is good.** -/
theorem leaf_good {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} {lo hi : ℕ → ℚ} {W : List Wit} {z : ℚ × ℚ}
    {β σ : ℕ → ℚ} (hV : VertTableOK ns V ν) (h : leafOK ns ⟨V, ν⟩ τ lo hi W z β σ = true) :
    GoodBox ns τ lo hi := by
  intro p hp K hK hD hB
  have F := leafOK_sound h p hp
  exact leaf_fan h p hp hK (hD (zmem_disk F.zmem)) fun w hw =>
    wit_mem_K hV hD hB (F.mem w hw).1 (F.mem w hw).2

/-- **A passing combination leaf is good.** -/
theorem comb_good {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} {lo hi : ℕ → ℚ}
    {fans : List (List Wit × (ℚ × ℚ) × (ℕ → ℚ) × (ℕ → ℚ) × ℚ)} (hV : VertTableOK ns V ν)
    (h : combOK ns ⟨V, ν⟩ τ lo hi fans = true) : GoodBox ns τ lo hi := by
  intro p hp K hK hD hB
  have hfans : ∀ F ∈ fans, fanOK ns ⟨V, ν⟩ lo hi F.1 F.2.1 F.2.2.1 F.2.2.2.1 = true := by
    have h' := h
    simp only [combOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h'
    exact fun F hF => (h'.1.1.2 F hF).2
  have hfm : ∀ F ∈ fans, (∀ w ∈ F.1, w.body ≤ ns.length ∧ memOK ns ⟨V, ν⟩ w = true) ∧
      dot2 F.2.1 F.2.1 < 1 / 4 := by
    intro F hF
    have := hfans F hF
    simp only [fanOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1.1.1.1.2, this.1.1.1.1.2⟩
  exact comb_fan h p hp hK (fun F hF => hD (zmem_disk (hfm F hF).2))
    fun F hF w hw => wit_mem_K hV hD hB ((hfm F hF).1 w hw).1 ((hfm F hF).1 w hw).2

/-! ## Trees -/

open LebesgueCover.Fast in
lemma tryProp_sound {ns : List ℕ} {bs : Array FBody} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} {lo hi : Array ℚ} {L : FLeaf}
    {pl : FPlace} {N : ℕ} {eps : Float} (h : tryProp ns bs V ν τ lo hi L pl N eps = true) :
    GoodBox ns τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) ∨ True := Or.inr trivial

open LebesgueCover.Fast in
lemma leaf_good_of_try {ns : List ℕ} {bs : Array FBody} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} {lo hi : Array ℚ} {L : FLeaf}
    {pl : FPlace} {N : ℕ} {eps : Float} (hV : VertTableOK ns V ν) (h : tryProp ns bs V ν τ lo hi L pl N eps = true) :
    GoodBox ns τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) := by
  unfold tryProp at h
  split at h
  · exact absurd h (by simp)
  · exact leaf_good hV (leafOKF_sound h)

open LebesgueCover.Fast in
lemma leaf_good_of_eval {ns : List ℕ} {bs : Array FBody} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} {lo hi : Array ℚ}
    (hV : VertTableOK ns V ν) (h : evalLeafB ns bs V ν τ lo hi = true) :
    GoodBox ns τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) := by
  unfold evalLeafB at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact leaf_good_of_try hV h
  · exact leaf_good_of_try hV h

open LebesgueCover.Fast in
lemma comb_good_of_eval {ns : List ℕ} {bs : Array FBody} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} {lo hi : Array ℚ}
    {fs : List (Bool × List ℤ × ℚ)} (hV : VertTableOK ns V ν) (h : evalCombB ns bs V ν τ lo hi fs = true) :
    GoodBox ns τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) := by
  unfold evalCombB at h
  dsimp only at h
  split_ifs at h
  · exact comb_good hV (combOKF_sound h)

lemma getD_set (arr : Array ℚ) (i a : ℕ) (v : ℚ) (hi : i < arr.size) :
    (arr.set! i v).getD a 0 = if a = i then v else arr.getD a 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  by_cases h : a = i
  · subst h; rw [if_pos rfl, Array.set!, Array.getElem?_setIfInBounds_self_of_lt hi]; rfl
  · rw [if_neg h, Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm h)]

lemma getD_eq_get (arr : Array ℚ) (i : ℕ) (hi : i < arr.size) : arr[i]! = arr.getD i 0 := by
  simp [Array.getD, hi]

open LebesgueCover.Fast in
lemma walk_suffix {ns : List ℕ} {bs : Array FBody} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} :
    ∀ (fuel : ℕ) (cs : List ℕ) (sd : List (List (Bool × List ℤ × ℚ))) (subs : List (Array ℚ × Array ℚ)) (lo hi : Array ℚ) r,
      walk ns bs V ν τ fuel cs sd subs lo hi = some r → ∀ b ∈ r.2.2, b ∈ subs := by
  intro fuel
  induction fuel with
  | zero => intro cs sd subs lo hi r h; simp [walk] at h
  | succ fuel ih =>
    intro cs sd subs lo hi r h b hb
    cases cs with
    | nil => simp [walk] at h
    | cons c cs =>
      unfold walk at h
      split_ifs at h with h1 h2 h3 h4
      · cases h; exact hb
      · cases sd with
        | nil => simp at h
        | cons f sd' => simp only at h; split_ifs at h; cases h; exact hb
      · cases subs with
        | nil => simp at h
        | cons b0 subs' =>
          simp only at h; split_ifs at h; cases h; exact List.mem_cons_of_mem _ hb
      · simp only at h
        cases hw1 : walk ns bs V ν τ fuel cs sd subs lo (hi.set! c ((lo[c]! + hi[c]!) / 2)) with
        | none => rw [hw1] at h; simp at h
        | some r1 =>
          rw [hw1] at h; simp only at h
          exact ih _ _ _ _ _ _ hw1 b (ih _ _ _ _ _ _ h b hb)

open LebesgueCover.Fast in
/-- **A passing tree walk is good** on its box, if the delegated boxes are good. -/
theorem walk_good {ns : List ℕ} {bs : Array FBody} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} (hV : VertTableOK ns V ν) :
    ∀ (fuel : ℕ) (cs : List ℕ) (sd : List (List (Bool × List ℤ × ℚ))) (subs : List (Array ℚ × Array ℚ)) (lo hi : Array ℚ) r,
      (∀ b ∈ subs, GoodBox ns τ (fun a => b.1.getD a 0) (fun a => b.2.getD a 0)) →
      walk ns bs V ν τ fuel cs sd subs lo hi = some r → GoodBox ns τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) := by
  intro fuel
  induction fuel with
  | zero => intro cs sd subs lo hi r _ h; simp [walk] at h
  | succ fuel ih =>
    intro cs sd subs lo hi r hsubs h
    cases cs with
    | nil => simp [walk] at h
    | cons c cs =>
      unfold walk at h
      by_cases h254 : c = 254
      · rw [if_pos h254] at h
        by_cases he : evalLeafB ns bs V ν τ lo hi = true
        · exact leaf_good_of_eval hV he
        · rw [if_neg he] at h; exact absurd h (by simp)
      · rw [if_neg h254] at h
        by_cases h252 : c = 252
        · rw [if_pos h252] at h
          cases sd with
          | nil => exact absurd h (by simp)
          | cons f sd' =>
            simp only at h
            by_cases he : evalCombB ns bs V ν τ lo hi f = true
            · exact comb_good_of_eval hV he
            · rw [if_neg he] at h; exact absurd h (by simp)
        · rw [if_neg h252] at h
          by_cases h250 : c = 250
          · rw [if_pos h250] at h
            cases subs with
            | nil => exact absurd h (by simp)
            | cons b subs' =>
              simp only at h
              by_cases hb : b.1 = lo ∧ b.2 = hi
              · have g := hsubs b List.mem_cons_self
                rw [hb.1, hb.2] at g; exact g
              · rw [if_neg hb] at h; exact absurd h (by simp)
          · rw [if_neg h250] at h
            by_cases hc : c < lo.size ∧ c < hi.size
            · rw [if_pos hc] at h
              simp only at h
              set m := (lo[c]! + hi[c]!) / 2 with hm
              cases hw1 : walk ns bs V ν τ fuel cs sd subs lo (hi.set! c m) with
              | none => rw [hw1] at h; exact absurd h (by simp)
              | some r1 =>
                rw [hw1] at h
                simp only at h
                have g1 := ih cs sd subs lo (hi.set! c m) r1 hsubs hw1
                have g2 := ih r1.1 r1.2.1 r1.2.2 (lo.set! c m) hi r
                  (fun b hb => hsubs b (walk_suffix _ _ _ _ _ _ _ hw1 b hb)) h
                intro p hp K hK hD hB
                by_cases hpc : (p c : ℝ) ≤ (m : ℝ)
                · refine g1 p (fun a ha => ?_) K hK hD hB
                  dsimp only
                  rw [getD_set _ _ _ _ hc.2]
                  split_ifs with hac
                  · subst hac; exact ⟨(hp a ha).1, hpc⟩
                  · exact hp a ha
                · push Not at hpc
                  refine g2 p (fun a ha => ?_) K hK hD hB
                  dsimp only
                  rw [getD_set _ _ _ _ hc.1]
                  split_ifs with hac
                  · subst hac; exact ⟨hpc.le, (hp a ha).2⟩
                  · exact hp a ha
            · rw [if_neg hc] at h; exact absurd h (by simp)

open LebesgueCover.Fast in
/-- **A passing cell is good.** -/
theorem checkCell_good {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} {lo hi : Array ℚ} {codes : List ℕ}
    {sd : List (List (Bool × List ℤ × ℚ))} (hV : VertTableOK ns V ν) (h : checkCell ns V ν τ lo hi codes sd = true) :
    GoodBox ns τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) := by
  unfold checkCell at h
  dsimp only at h
  split at h
  · rename_i r hr
    exact walk_good hV _ _ _ _ _ _ _ (fun b hb => by simp at hb) hr
  · exact absurd h (by simp)

open LebesgueCover.Fast in
theorem checkCellStr_good {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} {lo hi codes side : String}
    (hV : VertTableOK ns V ν) (h : checkCellStr ns V ν τ lo hi codes side = true) :
    GoodBox ns τ (fun a => (parseRatList lo).getD a 0) (fun a => (parseRatList hi).getD a 0) :=
  checkCell_good hV h

/-! ## Grid and blocks -/

lemma set_oob (arr : Array ℚ) (i : ℕ) (v : ℚ) (h : ¬ i < arr.size) : arr.set! i v = arr := by
  simp [Array.set!, Array.setIfInBounds, h]

/-- **Split.** Good halves give a good box. -/
lemma good_split {ns : List ℕ} {τ : ℚ} {lo hi : Array ℚ} (a : ℕ) (m : ℚ)
    (g1 : GoodBox ns τ (fun i => lo.getD i 0) (fun i => (hi.set! a m).getD i 0))
    (g2 : GoodBox ns τ (fun i => (lo.set! a m).getD i 0) (fun i => hi.getD i 0)) :
    GoodBox ns τ (fun i => lo.getD i 0) (fun i => hi.getD i 0) := by
  by_cases hhi : a < hi.size
  · by_cases hlo : a < lo.size
    · intro p hp K hK hD hB
      by_cases hpc : (p a : ℝ) ≤ (m : ℝ)
      · refine g1 p (fun b hb => ?_) K hK hD hB
        dsimp only
        rw [getD_set _ _ _ _ hhi]
        split_ifs with hab
        · subst hab; exact ⟨(hp b hb).1, hpc⟩
        · exact hp b hb
      · push Not at hpc
        refine g2 p (fun b hb => ?_) K hK hD hB
        dsimp only
        rw [getD_set _ _ _ _ hlo]
        split_ifs with hab
        · subst hab; exact ⟨hpc.le, (hp b hb).2⟩
        · exact hp b hb
    · rw [set_oob lo a m hlo] at g2; exact g2
  · rw [set_oob hi a m hhi] at g1; exact g1

open LebesgueCover.Fast in
lemma grid_good {ns : List ℕ} {τ : ℚ} :
    ∀ (sp : List ℕ) (lo hi : Array ℚ), (∀ c ∈ gridCells sp lo hi, GoodBox ns τ (fun i => c.1.getD i 0) (fun i => c.2.getD i 0)) →
      GoodBox ns τ (fun i => lo.getD i 0) (fun i => hi.getD i 0) := by
  intro sp
  induction sp with
  | nil => intro lo hi h; exact h (lo, hi) (by simp [gridCells])
  | cons a rest ih =>
    intro lo hi h
    simp only [gridCells, List.mem_append] at h
    exact good_split a _ (ih _ _ fun c hc => h c (Or.inl hc)) (ih _ _ fun c hc => h c (Or.inr hc))

open LebesgueCover.Fast in
lemma checkCells_good {ns : List ℕ} {bs : Array FBody} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} (hV : VertTableOK ns V ν) :
    ∀ (cells : List (Array ℚ × Array ℚ)) (codes : List ℕ) (sd : List (List (Bool × List ℤ × ℚ)))
      (subs : List (Array ℚ × Array ℚ)),
      (∀ b ∈ subs, GoodBox ns τ (fun a => b.1.getD a 0) (fun a => b.2.getD a 0)) →
      checkCells ns bs V ν τ cells codes sd subs = true →
        ∀ c ∈ cells, GoodBox ns τ (fun i => c.1.getD i 0) (fun i => c.2.getD i 0) := by
  intro cells
  induction cells with
  | nil => intro _ _ _ _ _ c hc; simp at hc
  | cons c0 cells ih =>
    intro codes sd subs hsubs h c hc
    obtain ⟨lo, hi⟩ := c0
    unfold checkCells at h
    split at h
    · rename_i codes' sd' subs' hw
      rcases List.mem_cons.mp hc with rfl | hc
      · exact walk_good hV _ _ _ _ _ _ _ hsubs hw
      · exact ih codes' sd' subs' (fun b hb => hsubs b (walk_suffix _ _ _ _ _ _ _ hw b hb)) h c hc
    · exact absurd h (by simp)

open LebesgueCover.Fast in
/-- **Blocks.** A passing block of cells is good, if its delegated boxes are good. -/
theorem block_good {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} (hV : VertTableOK ns V ν) {rl rh : Array ℚ}
    {d e start count : ℕ} {codes side : String} {subs : List (String × String)}
    (hsubs : ∀ p ∈ subs, GoodBox ns τ (fun a => (parseRatList p.1).getD a 0) (fun a => (parseRatList p.2).getD a 0))
    (h : checkBlockStr ns V ν τ rl rh d e start count codes side subs = true) :
    ∀ c ∈ ((gridCells (gridSplits d e) rl rh).drop start).take count,
      GoodBox ns τ (fun i => c.1.getD i 0) (fun i => c.2.getD i 0) := by
  unfold checkBlockStr at h
  refine checkCells_good hV _ _ _ _ (fun b hb => ?_) h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
  exact hsubs p hp

open LebesgueCover.Fast in
/-- **The root box** is good if blocks of `B` cells, `J` of them, all pass (with good delegated boxes) and cover
the grid. -/
theorem root_good {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} (hV : VertTableOK ns V ν) {rl rh : Array ℚ}
    {d e B J : ℕ} {cs sd : ℕ → String} {subs : ℕ → List (String × String)}
    (hsubs : ∀ j < J, ∀ p ∈ subs j,
      GoodBox ns τ (fun a => (parseRatList p.1).getD a 0) (fun a => (parseRatList p.2).getD a 0))
    (h : ∀ j < J, checkBlockStr ns V ν τ rl rh d e (j * B) B (cs j) (sd j) (subs j) = true)
    (hJ : (gridCells (gridSplits d e) rl rh).length ≤ J * B) :
    GoodBox ns τ (fun i => rl.getD i 0) (fun i => rh.getD i 0) := by
  apply grid_good
  intro c hc
  set L := gridCells (gridSplits d e) rl rh with hL
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0; rw [Nat.mul_zero] at hJ; omega
    · exact h0
  set j := i / B with hj
  have hjJ : j < J := by
    by_contra hc'; push Not at hc'
    have : J * B ≤ j * B := Nat.mul_le_mul_right B hc'
    have : j * B ≤ i := Nat.div_mul_le_self i B
    omega
  apply block_good hV (hsubs j hjJ) (h j hjJ)
  have h1 : j * B ≤ i := Nat.div_mul_le_self i B
  have h2 : i < j * B + B := Nat.lt_div_mul_add hB
  have hiL : i < L.length := hi
  have hLm : (gridCells (gridSplits d e) rl rh).length = L.length := rfl
  rw [List.mem_iff_getElem]
  refine ⟨i - j * B, ?_, ?_⟩
  · simp only [List.length_take, List.length_drop]
    generalize j * B = t at h1 h2 ⊢
    omega
  · simp only [List.getElem_take, List.getElem_drop]
    congr 1
    generalize j * B = t at h1 h2 ⊢
    omega

open LebesgueCover.Fast in
lemma gridCells_length : ∀ (sp : List ℕ) (lo hi : Array ℚ), (gridCells sp lo hi).length = 2 ^ sp.length := by
  intro sp
  induction sp with
  | nil => intro lo hi; simp [gridCells]
  | cons a rest ih => intro lo hi; simp only [gridCells, List.length_append, ih, List.length_cons]; ring

open LebesgueCover.Fast in
lemma gridSplits_length (d e : ℕ) : (gridSplits d e).length = d * e := by
  unfold gridSplits
  rw [List.length_flatMap]
  simp only [List.length_replicate]
  induction d with
  | zero => simp
  | succ d ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp; ring

open LebesgueCover.Fast in
/-- **The root box** is good if every block of `B` consecutive grid cells (`J` blocks covering the grid) is good. -/
theorem root_good' {ns : List ℕ} {τ : ℚ} {rl rh : Array ℚ} {d e B J : ℕ}
    (hblk : ∀ j < J, ∀ c ∈ ((gridCells (gridSplits d e) rl rh).drop (j * B)).take B,
      GoodBox ns τ (fun i => c.1.getD i 0) (fun i => c.2.getD i 0))
    (hJ : 2 ^ (d * e) ≤ J * B) :
    GoodBox ns τ (fun i => rl.getD i 0) (fun i => rh.getD i 0) := by
  apply grid_good
  intro c hc
  set L := gridCells (gridSplits d e) rl rh with hL
  have hlen : L.length = 2 ^ (d * e) := by rw [hL, gridCells_length, gridSplits_length]
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0; rw [Nat.mul_zero] at hJ; have := Nat.one_le_two_pow (n := d * e); omega
    · exact h0
  set j := i / B with hj
  have hjJ : j < J := by
    by_contra hc'; push Not at hc'
    have : J * B ≤ j * B := Nat.mul_le_mul_right B hc'
    have : j * B ≤ i := Nat.div_mul_le_self i B
    omega
  apply hblk j hjJ
  have h1 : j * B ≤ i := Nat.div_mul_le_self i B
  have h2 : i < j * B + B := Nat.lt_div_mul_add hB
  have hiL : i < L.length := hi
  have hLm : (gridCells (gridSplits d e) rl rh).length = L.length := rfl
  rw [List.mem_iff_getElem]
  refine ⟨i - j * B, ?_, ?_⟩
  · simp only [List.length_take, List.length_drop]
    generalize j * B = t at h1 h2 ⊢
    omega
  · simp only [List.getElem_take, List.getElem_drop]
    congr 1
    generalize j * B = t at h1 h2 ⊢
    omega

end LebesgueCover.Cert
