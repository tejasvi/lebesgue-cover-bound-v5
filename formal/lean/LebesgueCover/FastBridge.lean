import LebFast.Exact
import LebesgueCover.Sound

/-!
# The fast exact check implies the reference check

`leafOKF` (core Lean, compiled) organizes the computations of `LebesgueCover.Cert.leafOK` for speed. Here we prove
`leafOKF … = true → leafOK … = true`: the sparse fan rows equal the dense ones (the omitted coefficients vanish), the
filtered pair sums equal the full ones (the omitted terms vanish), and array lookups equal the functions they store.
-/

open Finset

namespace LebesgueCover.Fast

open LebesgueCover.Cert

/-! ## Basic identifications -/

lemma det2Q_eq (a b : ℚ × ℚ) : det2Q a b = det2 a b := rfl
lemma dot2Q_eq (a b : ℚ × ℚ) : dot2Q a b = dot2 a b := rfl
lemma rot2Q_eq (u q : ℚ × ℚ) : rot2Q u q = rot2 u q := rfl
lemma J2Q_eq (q : ℚ × ℚ) : J2Q q = J2 q := rfl
lemma uQF_eq (s : ℚ) : uQF s = uQ s := rfl
lemma yTxF_eq (i : ℕ) : yTxF i = yTx i := rfl
lemma yTyF_eq (i : ℕ) : yTyF i = yTy i := rfl
lemma yCF_eq (i : ℕ) : yCF i = yC i := rfl
lemma ySF_eq (i : ℕ) : ySF i = yS i := rfl
lemma yBodyF_eq (v : ℕ) : yBodyF v = yBody v := rfl
lemma yKindF_eq (v : ℕ) : yKindF v = yKind v := rfl

lemma rat_abs_eq (x : ℚ) : x.abs = |x| := by
  unfold Rat.abs; split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (lt_of_not_ge h)).symm

/-- `BBF` as the reference `BodyBox`. -/
def BBF.toBB (B : BBF) : BodyBox := ⟨B.tc, B.ht, B.M, B.Cmax, B.Smax, B.sOK⟩

lemma bodyBoxF_eq (lo hi : ℕ → ℚ) (i : ℕ) : (bodyBoxF lo hi i).toBB = bodyBox lo hi i := by
  unfold bodyBoxF bodyBox BBF.toBB
  split_ifs <;> simp [rat_abs_eq, uQF_eq, det2Q_eq, dot2Q_eq, bTxF, bTyF, bSF, bTx, bTy, bS]
  exact decide_eq_decide.mpr Iff.rfl

lemma yCentreF_eq (lo hi : ℕ → ℚ) (v : ℕ) :
    yCentreF (bodyBoxF lo hi) v = yCentre (bodyBox lo hi) v := by
  unfold yCentreF yCentre
  rw [← bodyBoxF_eq]; rfl

lemma yHalfF_eq (lo hi : ℕ → ℚ) (v : ℕ) :
    yHalfF (bodyBoxF lo hi) v = yHalf (bodyBox lo hi) v := by
  unfold yHalfF yHalf
  rw [← bodyBoxF_eq]; rfl

/-! ## Sums -/

lemma lsum_eq_sum (l : List ℕ) (f : ℕ → ℚ) : lsum l f = (l.map f).sum := by
  unfold lsum
  suffices h : ∀ c, l.foldl (fun acc a => acc + f a) c = c + (l.map f).sum by simpa using h 0
  induction l with
  | nil => intro c; simp
  | cons a t ih => intro c; simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [ih]; ring

lemma lsum_range (n : ℕ) (f : ℕ → ℚ) : lsum (List.range n) f = ∑ a ∈ range n, f a := by
  rw [lsum_eq_sum]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma lsum_nodup (S : List ℕ) (hS : S.Nodup) (f : ℕ → ℚ) : lsum S f = ∑ a ∈ S.toFinset, f a := by
  rw [lsum_eq_sum, List.sum_toFinset _ hS]

/-- The restricted quadratic bound equals the dense one when the omitted coefficients vanish. -/
lemma quadLowerAbsS_eq (n : ℕ) (S : List ℕ) (hS : S.Nodup) (hSn : ∀ a ∈ S, a < n) (c0 : ℚ) (g : ℕ → ℚ)
    (A : ℕ → ℕ → ℚ) (y0 w : ℕ → ℚ) (hg : ∀ a, a ∉ S → g a = 0) (hA : ∀ a b, (a ∉ S ∨ b ∉ S) → A a b = 0) :
    quadLowerAbsS S c0 g A y0 w = quadLowerAbs n c0 g A y0 w := by
  set T := S.toFinset with hT
  have hTn : T ⊆ range n := fun a ha => mem_range.mpr (hSn a (List.mem_toFinset.mp ha))
  have hmem : ∀ a, a ∈ T ↔ a ∈ S := fun a => List.mem_toFinset
  -- each Finset sum over `range n` reduces to `T`
  have r1 : ∀ f : ℕ → ℚ, (∀ a, a ∉ S → f a = 0) → ∑ a ∈ range n, f a = ∑ a ∈ T, f a := by
    intro f hf
    exact (Finset.sum_subset hTn fun a _ ha => hf a (fun h => ha ((hmem a).mpr h))).symm
  unfold quadLowerAbsS quadLowerAbs
  simp only [lsum_nodup S hS]
  rw [← hT]
  have e1 : ∑ a ∈ range n, g a * y0 a = ∑ a ∈ T, g a * y0 a := r1 _ fun a ha => by rw [hg a ha, zero_mul]
  have e2 : ∑ a ∈ range n, ∑ b ∈ range n, A a b * y0 a * y0 b = ∑ a ∈ T, ∑ b ∈ T, A a b * y0 a * y0 b := by
    rw [r1 _ fun a ha => Finset.sum_eq_zero fun b _ => by rw [hA a b (Or.inl ha)]; ring]
    exact Finset.sum_congr rfl fun a _ => r1 _ fun b hb => by rw [hA a b (Or.inr hb)]; ring
  have e3 : ∑ a ∈ range n, |g a + ∑ b ∈ range n, (A a b + A b a) * y0 b| * w a =
      ∑ a ∈ T, |g a + ∑ b ∈ T, (A a b + A b a) * y0 b| * w a := by
    rw [r1 _ fun a ha => by
      rw [hg a ha, Finset.sum_eq_zero fun b _ => by rw [hA a b (Or.inl ha), hA b a (Or.inr ha)]; ring]; simp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [r1 _ fun b hb => by rw [hA a b (Or.inr hb), hA b a (Or.inl hb)]; ring]
  have e4 : ∑ a ∈ range n, ∑ b ∈ range n, |A a b| * w a * w b = ∑ a ∈ T, ∑ b ∈ T, |A a b| * w a * w b := by
    rw [r1 _ fun a ha => Finset.sum_eq_zero fun b _ => by rw [hA a b (Or.inl ha)]; simp]
    exact Finset.sum_congr rfl fun a _ => r1 _ fun b hb => by rw [hA a b (Or.inr hb)]; simp
  rw [e1, e2, e3, e4]
  simp only [rat_abs_eq]

/-! ## Witnesses -/

def toWit (p : ℕ × (ℚ × ℚ)) : Wit := ⟨p.1, p.2⟩

lemma bodyBoxF_M (lo hi : ℕ → ℚ) (i : ℕ) : (bodyBoxF lo hi i).M = (bodyBox lo hi i).M := by
  rw [← bodyBoxF_eq]; rfl
lemma bodyBoxF_tc (lo hi : ℕ → ℚ) (i : ℕ) : (bodyBoxF lo hi i).tc = (bodyBox lo hi i).tc := by
  rw [← bodyBoxF_eq]; rfl
lemma bodyBoxF_sOK (lo hi : ℕ → ℚ) (i : ℕ) : (bodyBoxF lo hi i).sOK = (bodyBox lo hi i).sOK := by
  rw [← bodyBoxF_eq]; rfl

@[simp] lemma mkFWit_body (bb : ℕ → BBF) (i : ℕ) (q : ℚ × ℚ) : (mkFWit bb i q).body = i := by
  unfold mkFWit; split_ifs with h <;> simp [h]
@[simp] lemma mkFWit_pt (bb : ℕ → BBF) (i : ℕ) (q : ℚ × ℚ) : (mkFWit bb i q).pt = q := by
  unfold mkFWit; split_ifs <;> rfl

lemma mkFWit_X0 (lo hi : ℕ → ℚ) (i : ℕ) (q : ℚ × ℚ) :
    (mkFWit (bodyBoxF lo hi) i q).X0 = witX0 (bodyBox lo hi) ⟨i, q⟩ := by
  unfold mkFWit witX0
  split_ifs with h
  · rfl
  · simp only [bodyBoxF_M, bodyBoxF_tc, rot2Q_eq]

lemma witLF_eq (lo hi : ℕ → ℚ) (i : ℕ) (q : ℚ × ℚ) :
    witLF (mkFWit (bodyBoxF lo hi) i q) = witL (bodyBox lo hi) ⟨i, q⟩ := by
  funext v
  unfold witLF witL mkFWit
  by_cases h : i = 0
  · simp [h]
  · simp only [h, if_false, bodyBoxF_M, rot2Q_eq, J2Q_eq, yTxF_eq, yTyF_eq, yCF_eq, ySF_eq]

lemma mem_varsOf {i a : ℕ} (h : a ∈ varsOf i) : 1 ≤ i ∧ yBody a = i ∧ a < 4 * i - 2 := by
  unfold varsOf at h
  split_ifs at h with h0 h1
  · simp at h
  · subst h1; simp at h; rcases h with rfl | rfl <;> simp [yBody]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    refine ⟨by omega, ?_, by omega⟩
    unfold yBody
    rcases h with rfl | rfl | rfl | rfl <;> (split_ifs <;> omega)

lemma varsOf_nodup (i : ℕ) : (varsOf i).Nodup := by
  unfold varsOf; split_ifs with h0 h1
  · simp
  · simp
  · have hi : 2 ≤ i := by omega
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]; omega
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]; omega
    · simp only [List.mem_singleton]; omega

lemma witL_zero (bb : ℕ → BodyBox) (w : Wit) (v : ℕ) (hv : v ∉ varsOf w.body) : witL bb w v = (0, 0) := by
  unfold witL
  by_cases h0 : w.body = 0
  · simp [h0]
  · simp only [h0, if_false]
    have h1 : v ≠ yTx w.body := by
      intro e; apply hv; unfold varsOf yTx at *; split_ifs at * <;> simp_all
    have h2 : v ≠ yTy w.body := by
      intro e; apply hv; unfold varsOf yTy at *; split_ifs at * <;> simp_all
    have h3 : ¬(2 ≤ w.body ∧ v = yC w.body) := by
      rintro ⟨h, e⟩; apply hv; unfold varsOf yC at *; split_ifs <;> simp_all <;> omega
    have h4 : ¬(2 ≤ w.body ∧ v = yS w.body) := by
      rintro ⟨h, e⟩; apply hv; unfold varsOf yS at *; split_ifs <;> simp_all <;> omega
    simp only [h1, h2, h3, h4, if_false]

lemma pairVars_nodup (w w' : FWit) : (pairVars w w').Nodup := by
  unfold pairVars; split_ifs with h
  · exact varsOf_nodup _
  · rw [List.nodup_append]
    refine ⟨varsOf_nodup _, varsOf_nodup _, fun a ha b hb e => ?_⟩
    subst e
    exact h ((mem_varsOf ha).2.1.symm.trans (mem_varsOf hb).2.1)

lemma mem_pairVars {w w' : FWit} {a : ℕ} : a ∈ pairVars w w' ↔ a ∈ varsOf w.body ∨ a ∈ varsOf w'.body := by
  unfold pairVars; split_ifs with h
  · rw [← h]; simp
  · simp [List.mem_append]

/-- **Fan rows.** -/
lemma fanRowF_eq (lo hi : ℕ → ℚ) (k : ℕ) (z : ℚ × ℚ) (i i' : ℕ) (q q' : ℚ × ℚ) (hi1 : i ≤ k) (hi2 : i' ≤ k) :
    fanRowF (yCentreF (bodyBoxF lo hi)) (yHalfF (bodyBoxF lo hi)) z (mkFWit (bodyBoxF lo hi) i q)
      (mkFWit (bodyBoxF lo hi) i' q') = fanRow (4 * k - 2) (bodyBox lo hi) z ⟨i, q⟩ ⟨i', q'⟩ := by
  unfold fanRowF fanRow
  have hy0 : yCentreF (bodyBoxF lo hi) = yCentre (bodyBox lo hi) := funext (yCentreF_eq lo hi)
  have hw : yHalfF (bodyBoxF lo hi) = yHalf (bodyBox lo hi) := funext (yHalfF_eq lo hi)
  rw [hy0, hw, witLF_eq, witLF_eq, mkFWit_X0, mkFWit_X0]
  apply quadLowerAbsS_eq _ _ (pairVars_nodup _ _)
  · intro a ha
    rcases mem_pairVars.mp ha with h | h <;> (have := mem_varsOf h; simp at this; omega)
  · intro a ha
    rw [mem_pairVars] at ha; push Not at ha
    simp only [pairGF, pairG, det2Q_eq]
    rw [witL_zero _ _ a (by simpa using ha.2), witL_zero _ _ a (by simpa using ha.1)]
    simp [det2]
  · intro a b hab
    simp only [pairAF, pairA, det2Q_eq]
    rcases hab with h | h
    · rw [mem_pairVars] at h; push Not at h
      rw [witL_zero _ _ a (by simpa using h.1)]; simp [det2]
    · rw [mem_pairVars] at h; push Not at h
      rw [witL_zero _ _ b (by simpa using h.2)]; simp [det2]

/-! ## Pair lists -/

lemma cycPairs_map {α β : Type} (f : α → β) (l : List α) :
    cycPairs (l.map f) = (cycPairs l).map (Prod.map f f) := by
  cases l with
  | nil => rfl
  | cons a t =>
    simp only [List.map_cons, cycPairs]
    rw [show List.map f t ++ [f a] = List.map f (t ++ [a]) by simp, ← List.map_cons, List.zip_map]

lemma cycPairsF_eq {α : Type} (l : List α) : cycPairsF l = cycPairs l := by
  cases l <;> rfl

lemma sum_filter_eq {α : Type} (l : List α) (q : α → Bool) (f : α → ℚ) (h : ∀ x ∈ l, q x = false → f x = 0) :
    ((l.filter q).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih fun x hx => h x (by simp [hx])
    by_cases hq : q a = true
    · simp [List.filter_cons, hq, ih']
    · have hf := h a (by simp) (by simpa using hq)
      simp [List.filter_cons, hq, ih', hf]

/-- The fast pair list and the reference pair list, as images of one list. -/
def mkPair (lo hi : ℕ → ℚ) (pr : (ℕ × (ℚ × ℚ)) × (ℕ × (ℚ × ℚ))) : FWit × FWit :=
  (mkFWit (bodyBoxF lo hi) pr.1.1 pr.1.2, mkFWit (bodyBoxF lo hi) pr.2.1 pr.2.2)

lemma prsF_eq (lo hi : ℕ → ℚ) (W : List (ℕ × (ℚ × ℚ))) :
    cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q) = (cycPairs W).map (mkPair lo hi) := by
  rw [cycPairsF_eq, cycPairs_map]; rfl

lemma prs_eq (W : List (ℕ × (ℚ × ℚ))) : cycPairs (W.map toWit) = (cycPairs W).map (Prod.map toWit toWit) :=
  cycPairs_map _ _

lemma witL_ne_body {bb : ℕ → BodyBox} {w : Wit} {a : ℕ} (h : witL bb w a ≠ (0, 0)) : w.body = yBody a := by
  by_contra hne
  apply h
  apply witL_zero
  intro ha
  exact hne (mem_varsOf ha).2.1.symm

/-! ## Fan-area coefficients -/

lemma fanGval_eq (lo hi : ℕ → ℚ) (W : List (ℕ × (ℚ × ℚ))) (β : ℕ → ℚ) (a : ℕ) :
    fanGval (cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)) β a =
      (fanQuad (bodyBox lo hi) (W.map toWit) β).g a := by
  unfold fanGval fanQuad
  simp only []
  rw [prsF_eq, prs_eq, yBodyF_eq, yKindF_eq]
  congr 1
  rw [List.filter_map, List.map_map, List.map_map, sum_filter_eq]
  · congr 1; apply List.map_congr_left; intro pr _
    simp only [Function.comp, mkPair, Prod.map, toWit, mkFWit_X0, witLF_eq, pairGF, pairG, det2Q_eq]
  · intro pr _ hq
    simp only [Function.comp, mkPair, mkFWit_body, decide_eq_false_iff_not, not_or] at hq
    simp only [Function.comp, mkPair, pairGF, det2Q_eq, witLF_eq, mkFWit_X0]
    have h1 : witL (bodyBox lo hi) ⟨pr.1.1, pr.1.2⟩ a = (0, 0) := by
      by_contra hc; exact hq.1 (witL_ne_body hc)
    have h2 : witL (bodyBox lo hi) ⟨pr.2.1, pr.2.2⟩ a = (0, 0) := by
      by_contra hc; exact hq.2 (witL_ne_body hc)
    rw [h1, h2]; simp [det2]

lemma fanHval_eq (lo hi : ℕ → ℚ) (W : List (ℕ × (ℚ × ℚ))) (β : ℕ → ℚ) (a b : ℕ) :
    fanHval (cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)) β a b =
      (fanQuad (bodyBox lo hi) (W.map toWit) β).H a b := by
  unfold fanHval fanQuad
  simp only []
  rw [prsF_eq, prs_eq, yBodyF_eq, yBodyF_eq, yKindF_eq]
  congr 1
  have split : ∀ (l : List ((ℕ × (ℚ × ℚ)) × (ℕ × (ℚ × ℚ)))),
      ((l.map (Prod.map toWit toWit)).map fun (w, w') =>
        (pairA (witL (bodyBox lo hi) w) (witL (bodyBox lo hi) w') a b +
          pairA (witL (bodyBox lo hi) w) (witL (bodyBox lo hi) w') b a) / 2).sum =
      ((l.map (Prod.map toWit toWit)).map fun (w, w') =>
        pairA (witL (bodyBox lo hi) w) (witL (bodyBox lo hi) w') a b / 2).sum +
      ((l.map (Prod.map toWit toWit)).map fun (w, w') =>
        pairA (witL (bodyBox lo hi) w) (witL (bodyBox lo hi) w') b a / 2).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x t ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [split]
  congr 1
  · rw [List.filter_map, List.map_map, List.map_map, sum_filter_eq]
    · congr 1; apply List.map_congr_left; intro pr _
      simp only [Function.comp, mkPair, Prod.map, toWit, witLF_eq, pairAF, pairA, det2Q_eq]
    · intro pr _ hq
      simp only [Function.comp, mkPair, mkFWit_body, decide_eq_false_iff_not, not_and_or] at hq
      simp only [Function.comp, mkPair, pairAF, det2Q_eq, witLF_eq]
      rcases hq with hq | hq
      · have h1 : witL (bodyBox lo hi) ⟨pr.1.1, pr.1.2⟩ a = (0, 0) := by
          by_contra hc; exact hq (witL_ne_body hc)
        rw [h1]; simp [det2]
      · have h2 : witL (bodyBox lo hi) ⟨pr.2.1, pr.2.2⟩ b = (0, 0) := by
          by_contra hc; exact hq (witL_ne_body hc)
        rw [h2]; simp [det2]
  · rw [List.filter_map, List.map_map, List.map_map, sum_filter_eq]
    · congr 1; apply List.map_congr_left; intro pr _
      simp only [Function.comp, mkPair, Prod.map, toWit, witLF_eq, pairAF, pairA, det2Q_eq]
    · intro pr _ hq
      simp only [Function.comp, mkPair, mkFWit_body, decide_eq_false_iff_not, not_and_or] at hq
      simp only [Function.comp, mkPair, pairAF, det2Q_eq, witLF_eq]
      rcases hq with hq | hq
      · have h1 : witL (bodyBox lo hi) ⟨pr.1.1, pr.1.2⟩ b = (0, 0) := by
          by_contra hc; exact hq (witL_ne_body hc)
        rw [h1]; simp [det2]
      · have h2 : witL (bodyBox lo hi) ⟨pr.2.1, pr.2.2⟩ a = (0, 0) := by
          by_contra hc; exact hq (witL_ne_body hc)
        rw [h2]; simp [det2]

lemma F0_eq (lo hi : ℕ → ℚ) (W : List (ℕ × (ℚ × ℚ))) (β : ℕ → ℚ) :
    ((cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)).map fun (w, w') => pairC0F w.X0 w'.X0 / 2).sum =
      (fanQuad (bodyBox lo hi) (W.map toWit) β).F0 := by
  unfold fanQuad
  simp only []
  rw [prsF_eq, prs_eq, List.map_map, List.map_map]
  congr 1; apply List.map_congr_left; intro pr _
  simp only [Function.comp, mkPair, Prod.map, toWit, mkFWit_X0, pairC0F, pairC0, det2Q_eq]

/-! ## PSD certificate, bound, winding, membership -/

lemma ldl_fst (n : ℕ) (N : ℕ → ℕ → ℚ) (a b : ℕ) : (ldl n N).1 a b = ((ldlF n N).1[a]!)[b]! := rfl
lemma ldl_snd (n : ℕ) (N : ℕ → ℕ → ℚ) (a : ℕ) : (ldl n N).2 a = (ldlF n N).2[a]! := rfl

lemma psdOKF_eq (n : ℕ) (N : ℕ → ℕ → ℚ) : psdOKF n N = psdOK n N := by
  unfold psdOKF psdOK
  simp only [lsum_range, ← ldl_fst, ← ldl_snd]
  congr 1

lemma windOKF_eq (lo hi : ℕ → ℚ) (W : List (ℕ × (ℚ × ℚ))) (z : ℚ × ℚ) :
    windOKF z (cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)) = windOK (bodyBox lo hi) z (W.map toWit) := by
  unfold windOKF windOK
  simp only [prsF_eq, prs_eq, List.map_map, Function.comp_def, mkPair, Prod.map, toWit, mkFWit_X0, det2Q_eq,
    dot2Q_eq, angleUBF, angleUB]
  congr 1

lemma memOKF_eq (ns : List ℕ) (V : ℕ → ℕ → ℚ × ℚ) (ν : ℚ) (bb : ℕ → BBF) (i : ℕ) (q : ℚ × ℚ) :
    memOKF ns V ν (mkFWit bb i q) = memOK ns ⟨V, ν⟩ ⟨i, q⟩ := by
  unfold memOKF memOK
  simp only [mkFWit_body, mkFWit_pt]
  split_ifs
  · exact decide_eq_decide.mpr (by rfl)
  · congr 1

/-! ## The bound and the main theorem -/

lemma mem_cycPairs_mem {α : Type} {W : List α} {pr : α × α} (h : pr ∈ cycPairs W) : pr.1 ∈ W ∧ pr.2 ∈ W := by
  cases W with
  | nil => simp [cycPairs] at h
  | cons a t =>
    simp only [cycPairs] at h
    have h1 := List.of_mem_zip h
    refine ⟨h1.1, ?_⟩
    rcases List.mem_append.mp h1.2 with h2 | h2
    · exact List.mem_cons_of_mem a h2
    · rw [List.mem_singleton.mp h2]; exact List.mem_cons_self

lemma arr_range_map {α : Type} [Inhabited α] (n : ℕ) (f : ℕ → α) (a : ℕ) (h : a < n) :
    ((Array.range n).map f)[a]! = f a := by
  simp [h]

lemma fanLowerF_eq (lo hi : ℕ → ℚ) (k : ℕ) (W : List (ℕ × (ℚ × ℚ))) (β σ : ℕ → ℚ) :
    fanLowerF (4 * k - 2) (yCentreF (bodyBoxF lo hi)) (yHalfF (bodyBoxF lo hi))
      ((cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)).map fun (w, w') => pairC0F w.X0 w'.X0 / 2).sum
      (fanGF (4 * k - 2) (cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)) β)
      (fanHF (4 * k - 2) (cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)) β) σ =
    fanLower (4 * k - 2) (bodyBox lo hi) (fanQuad (bodyBox lo hi) (W.map toWit) β) σ := by
  set prs := cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q) with hprs
  have hy0 : yCentreF (bodyBoxF lo hi) = yCentre (bodyBox lo hi) := funext (yCentreF_eq lo hi)
  have hw : yHalfF (bodyBoxF lo hi) = yHalf (bodyBox lo hi) := funext (yHalfF_eq lo hi)
  have hg : ∀ a ∈ range (4 * k - 2), (fanGF (4 * k - 2) prs β)[a]! = (fanQuad (bodyBox lo hi) (W.map toWit) β).g a := by
    intro a ha
    unfold fanGF
    rw [arr_range_map _ _ _ (mem_range.mp ha), hprs, fanGval_eq]
  have hH : ∀ a ∈ range (4 * k - 2), ∀ b ∈ range (4 * k - 2),
      ((fanHF (4 * k - 2) prs β)[a]!)[b]! = (fanQuad (bodyBox lo hi) (W.map toWit) β).H a b := by
    intro a ha b hb
    unfold fanHF
    rw [arr_range_map _ _ _ (mem_range.mp ha), arr_range_map _ _ _ (mem_range.mp hb), hprs, fanHval_eq]
  unfold fanLowerF fanLower
  simp only [lsum_range, hy0, hw, rat_abs_eq]
  rw [hprs, F0_eq lo hi W β, ← hprs]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        exact Finset.sum_congr rfl fun a ha => by rw [hg a ha]
      · congr 1
        exact Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => by rw [hH a ha b hb]
    · exact Finset.sum_congr rfl fun a ha => by
        rw [hg a ha, Finset.sum_congr rfl fun b hb => by rw [hH a ha b hb]]

/-- **Bridge.** The fast check implies the reference check. -/
theorem leafOKF_sound {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} {lo hi : ℕ → ℚ} {W : List (ℕ × (ℚ × ℚ))}
    {z : ℚ × ℚ} {β σ : ℕ → ℚ} (h : leafOKF ns V ν τ lo hi W z β σ = true) :
    leafOK ns ⟨V, ν⟩ τ lo hi (W.map toWit) z β σ = true := by
  set k := ns.length with hk
  -- the array-based functions are the plain ones
  have hbb : (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i)
      = bodyBoxF lo hi := by
    funext i; split_ifs with hi; · exact arr_range_map _ _ _ (by omega)
    · rfl
  have hy0 : (fun v => if v < 4 * k - 2 then ((Array.range (4 * k - 2)).map fun v => yCentreF (bodyBoxF lo hi) v)[v]!
      else yCentreF (bodyBoxF lo hi) v) = yCentreF (bodyBoxF lo hi) := by
    funext v; split_ifs with hv; · exact arr_range_map _ _ _ hv
    · rfl
  have hwv : (fun v => if v < 4 * k - 2 then ((Array.range (4 * k - 2)).map fun v => yHalfF (bodyBoxF lo hi) v)[v]!
      else yHalfF (bodyBoxF lo hi) v) = yHalfF (bodyBoxF lo hi) := by
    funext v; split_ifs with hv; · exact arr_range_map _ _ _ hv
    · rfl
  have hcore : leafOKCore ns V ν τ W z β σ (bodyBoxF lo hi) (yCentreF (bodyBoxF lo hi)) (yHalfF (bodyBoxF lo hi)) = true := by
    have e : leafOKF ns V ν τ lo hi W z β σ = leafOKCore ns V ν τ W z β σ
        (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i)
        (fun v => if v < 4 * k - 2 then ((Array.range (4 * k - 2)).map fun v => yCentreF
          (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i) v)[v]!
          else yCentreF
          (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i) v)
        (fun v => if v < 4 * k - 2 then ((Array.range (4 * k - 2)).map fun v => yHalfF
          (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i) v)[v]!
          else yHalfF
          (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i) v) :=
      rfl
    rw [e, hbb, hy0, hwv] at h
    exact h
  -- unpack the core
  unfold leafOKCore at hcore
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hcore
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsok, hk2⟩, hlen⟩, hmem⟩, hz⟩, hrows⟩, hwind⟩, hσ⟩, hpsd⟩, hbound⟩ := hcore
  rw [← hk] at *
  -- the witnesses' bodies are at most k
  have hbody : ∀ x ∈ W, x.1 ≤ k := fun x hx => by
    have := hmem (mkFWit (bodyBoxF lo hi) x.1 x.2) (List.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa using this.1
  unfold leafOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, hk2⟩, by simpa using hlen⟩, ?_⟩, by simpa [dot2Q_eq] using hz⟩, ?_⟩, ?_⟩, hσ⟩, ?_⟩, ?_⟩
  · intro i hi; rw [← bodyBoxF_sOK]; exact hsok i hi
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    have := hmem (mkFWit (bodyBoxF lo hi) x.1 x.2) (List.mem_map.mpr ⟨x, hx, rfl⟩)
    refine ⟨by simpa [toWit] using this.1, ?_⟩
    rw [← memOKF_eq ns V ν (bodyBoxF lo hi)]
    exact this.2
  · intro pr hpr
    rw [prs_eq] at hpr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpr
    have hx1 : x.1 ∈ W := (mem_cycPairs_mem hx).1
    have hx2 : x.2 ∈ W := (mem_cycPairs_mem hx).2
    have := hrows (mkPair lo hi x) (by rw [prsF_eq]; exact List.mem_map.mpr ⟨x, hx, rfl⟩)
    simp only [mkPair] at this
    rw [fanRowF_eq lo hi k z _ _ _ _ (hbody _ hx1) (hbody _ hx2)] at this
    exact this
  · rw [← windOKF_eq]; exact hwind
  · have eH : (fun a b => (if a < 4 * k - 2 ∧ b < 4 * k - 2 then
        ((fanHF (4 * k - 2) (cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)) β)[a]!)[b]!
        else fanHval (cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)) β a b) +
          if a = b then σ a else 0) =
        fun a b => (fanQuad (bodyBox lo hi) (W.map toWit) β).H a b + if a = b then σ a else 0 := by
      funext a b
      congr 1
      split_ifs with hab
      · unfold fanHF; rw [arr_range_map _ _ _ hab.1, arr_range_map _ _ _ hab.2, fanHval_eq]
      · rw [fanHval_eq]
    rw [eH, psdOKF_eq] at hpsd
    exact hpsd
  · rw [fanLowerF_eq] at hbound
    exact hbound

/-! ## Combination leaves -/

lemma fanCore_ok {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν : ℚ} {lo hi : ℕ → ℚ} {W : List (ℕ × (ℚ × ℚ))}
    {z : ℚ × ℚ} {β σ : ℕ → ℚ}
    (h : (fanCore ns V ν W z β σ (bodyBoxF lo hi) (yCentreF (bodyBoxF lo hi)) (yHalfF (bodyBoxF lo hi))).ok = true) :
    fanOK ns ⟨V, ν⟩ lo hi (W.map toWit) z β σ = true := by
  set k := ns.length with hk
  unfold fanCore at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hlen, hmem⟩, hz⟩, hrows⟩, hwind⟩, hσ⟩, hpsd⟩ := h
  rw [← hk] at *
  have hbody : ∀ x ∈ W, x.1 ≤ k := fun x hx => by
    have := hmem (mkFWit (bodyBoxF lo hi) x.1 x.2) (List.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa using this.1
  unfold fanOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨by simpa using hlen, ?_⟩, by simpa [dot2Q_eq] using hz⟩, ?_⟩, ?_⟩, hσ⟩, ?_⟩
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    have := hmem (mkFWit (bodyBoxF lo hi) x.1 x.2) (List.mem_map.mpr ⟨x, hx, rfl⟩)
    refine ⟨by simpa [toWit] using this.1, ?_⟩
    rw [← memOKF_eq ns V ν (bodyBoxF lo hi)]
    exact this.2
  · intro pr hpr
    rw [prs_eq] at hpr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpr
    have hx1 : x.1 ∈ W := (mem_cycPairs_mem hx).1
    have hx2 : x.2 ∈ W := (mem_cycPairs_mem hx).2
    have := hrows (mkPair lo hi x) (by rw [prsF_eq]; exact List.mem_map.mpr ⟨x, hx, rfl⟩)
    simp only [mkPair] at this
    rw [fanRowF_eq lo hi k z _ _ _ _ (hbody _ hx1) (hbody _ hx2)] at this
    exact this
  · rw [← windOKF_eq]; exact hwind
  · have eH : (fun a b => (if a < 4 * k - 2 ∧ b < 4 * k - 2 then
        ((fanHF (4 * k - 2) (cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)) β)[a]!)[b]!
        else fanHval (cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q)) β a b) +
          if a = b then σ a else 0) =
        fun a b => (fanQuad (bodyBox lo hi) (W.map toWit) β).H a b + if a = b then σ a else 0 := by
      funext a b
      congr 1
      split_ifs with hab
      · unfold fanHF; rw [arr_range_map _ _ _ hab.1, arr_range_map _ _ _ hab.2, fanHval_eq]
      · rw [fanHval_eq]
    rw [eH, psdOKF_eq] at hpsd
    exact hpsd

lemma fanCore_A (ns : List ℕ) (V : ℕ → ℕ → ℚ × ℚ) (ν : ℚ) (lo hi : ℕ → ℚ) (W : List (ℕ × (ℚ × ℚ)))
    (z : ℚ × ℚ) (β σ : ℕ → ℚ) :
    (fanCore ns V ν W z β σ (bodyBoxF lo hi) (yCentreF (bodyBoxF lo hi)) (yHalfF (bodyBoxF lo hi))).A =
      fanA (4 * ns.length - 2) (bodyBox lo hi) (fanQuad (bodyBox lo hi) (W.map toWit) β) σ := by
  set k := ns.length with hk
  set prs := cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q) with hprs
  have hy0 : yCentreF (bodyBoxF lo hi) = yCentre (bodyBox lo hi) := funext (yCentreF_eq lo hi)
  have hw : yHalfF (bodyBoxF lo hi) = yHalf (bodyBox lo hi) := funext (yHalfF_eq lo hi)
  have hg : ∀ a ∈ range (4 * k - 2), (fanGF (4 * k - 2) prs β)[a]! = (fanQuad (bodyBox lo hi) (W.map toWit) β).g a := by
    intro a ha; unfold fanGF; rw [arr_range_map _ _ _ (mem_range.mp ha), hprs, fanGval_eq]
  have hH : ∀ a ∈ range (4 * k - 2), ∀ b ∈ range (4 * k - 2),
      ((fanHF (4 * k - 2) prs β)[a]!)[b]! = (fanQuad (bodyBox lo hi) (W.map toWit) β).H a b := by
    intro a ha b hb; unfold fanHF
    rw [arr_range_map _ _ _ (mem_range.mp ha), arr_range_map _ _ _ (mem_range.mp hb), hprs, fanHval_eq]
  unfold fanCore fanA
  simp only [lsum_range, hy0, hw]
  rw [← hk, ← hprs, hprs, F0_eq lo hi W β, ← hprs]
  congr 1
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun a ha => by rw [hg a ha]
  · congr 1
    exact Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => by rw [hH a ha b hb]

lemma fanCore_G (ns : List ℕ) (V : ℕ → ℕ → ℚ × ℚ) (ν : ℚ) (lo hi : ℕ → ℚ) (W : List (ℕ × (ℚ × ℚ)))
    (z : ℚ × ℚ) (β σ : ℕ → ℚ) (a : ℕ) (ha : a < 4 * ns.length - 2) :
    (fanCore ns V ν W z β σ (bodyBoxF lo hi) (yCentreF (bodyBoxF lo hi)) (yHalfF (bodyBoxF lo hi))).G[a]! =
      fanG (4 * ns.length - 2) (bodyBox lo hi) (fanQuad (bodyBox lo hi) (W.map toWit) β) a := by
  set k := ns.length with hk
  set prs := cycPairsF (W.map fun (i, q) => mkFWit (bodyBoxF lo hi) i q) with hprs
  have hy0 : yCentreF (bodyBoxF lo hi) = yCentre (bodyBox lo hi) := funext (yCentreF_eq lo hi)
  have hH : ∀ b ∈ range (4 * k - 2),
      ((fanHF (4 * k - 2) prs β)[a]!)[b]! = (fanQuad (bodyBox lo hi) (W.map toWit) β).H a b := by
    intro b hb; unfold fanHF
    rw [arr_range_map _ _ _ ha, arr_range_map _ _ _ (mem_range.mp hb), hprs, fanHval_eq]
  unfold fanCore fanG
  simp only [lsum_range, hy0]
  rw [arr_range_map _ _ _ ha]
  rw [← hk, ← hprs]
  congr 1
  · unfold fanGF; rw [arr_range_map _ _ _ ha, hprs, fanGval_eq]
  · exact Finset.sum_congr rfl fun b hb => by rw [hH b hb]

/-- **Bridge for combination leaves.** -/
theorem combOKF_sound {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} {lo hi : ℕ → ℚ}
    {fans : List (List (ℕ × (ℚ × ℚ)) × (ℚ × ℚ) × (ℕ → ℚ) × (ℕ → ℚ) × ℚ)}
    (h : combOKF ns V ν τ lo hi fans = true) :
    combOK ns ⟨V, ν⟩ τ lo hi (fans.map fun F => (F.1.map toWit, F.2)) = true := by
  set k := ns.length with hk
  have hbb : (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i)
      = bodyBoxF lo hi := by
    funext i; split_ifs with hi; · exact arr_range_map _ _ _ (by omega)
    · rfl
  have hy0 : (fun v => if v < 4 * k - 2 then ((Array.range (4 * k - 2)).map fun v => yCentreF (bodyBoxF lo hi) v)[v]!
      else yCentreF (bodyBoxF lo hi) v) = yCentreF (bodyBoxF lo hi) := by
    funext v; split_ifs with hv; · exact arr_range_map _ _ _ hv
    · rfl
  have hwv : (fun v => if v < 4 * k - 2 then ((Array.range (4 * k - 2)).map fun v => yHalfF (bodyBoxF lo hi) v)[v]!
      else yHalfF (bodyBoxF lo hi) v) = yHalfF (bodyBoxF lo hi) := by
    funext v; split_ifs with hv; · exact arr_range_map _ _ _ hv
    · rfl
  have hcore : combOKCore ns V ν τ fans (bodyBoxF lo hi) (yCentreF (bodyBoxF lo hi)) (yHalfF (bodyBoxF lo hi)) = true := by
    have e : combOKF ns V ν τ lo hi fans = combOKCore ns V ν τ fans
        (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i)
        (fun v => if v < 4 * k - 2 then ((Array.range (4 * k - 2)).map fun v => yCentreF
          (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i) v)[v]!
          else yCentreF
          (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i) v)
        (fun v => if v < 4 * k - 2 then ((Array.range (4 * k - 2)).map fun v => yHalfF
          (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i) v)[v]!
          else yHalfF
          (fun i => if i ≤ k then ((Array.range (k + 1)).map fun i => bodyBoxF lo hi i)[i]! else bodyBoxF lo hi i) v) :=
      rfl
    rw [e, hbb, hy0, hwv] at h
    exact h
  unfold combOKCore at hcore
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, List.mem_map] at hcore
  obtain ⟨⟨⟨⟨hsok, hk2⟩, hfans⟩, hS⟩, hbound⟩ := hcore
  rw [← hk] at *
  unfold combOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  -- the weight sums agree
  have hSeq : ((fans.map fun F => (F.1.map toWit, F.2)).map fun F => F.2.2.2.2).sum =
      ((fans.map fun F => (F.2.2.2.2, fanCore ns V ν F.1 F.2.1 F.2.2.1 F.2.2.2.1 (bodyBoxF lo hi)
        (yCentreF (bodyBoxF lo hi)) (yHalfF (bodyBoxF lo hi)))).map fun (c : ℚ × FanC) => c.1).sum := by
    simp only [List.map_map]; rfl
  refine ⟨⟨⟨⟨?_, hk2⟩, ?_⟩, by rw [hSeq]; exact hS⟩, ?_⟩
  · intro i hi; rw [← bodyBoxF_sOK]; exact hsok i hi
  · intro F hF
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
    obtain ⟨h1, h2⟩ := hfans _ ⟨G, hG, rfl⟩
    exact ⟨h1, fanCore_ok h2⟩
  · rw [hSeq]
    convert hbound using 2
    · simp only [List.map_map]
      congr 1; apply List.map_congr_left; intro F _
      simp only [Function.comp, fanCore_A]
    · rw [lsum_range]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [rat_abs_eq]
      congr 2
      · simp only [List.map_map]
        congr 1; apply List.map_congr_left; intro F _
        simp only [Function.comp, fanCore_G ns V ν lo hi _ _ _ _ a (mem_range.mp ha)]
      · exact (yHalfF_eq lo hi a).symm

end LebesgueCover.Fast
