import LebesgueCover.Main5
import LebesgueCover.Diam
import L11.C0
import L11.C1
import L11.C2
import L11.C3
import L11.C4
import L11.C5
import L11.C6
import L11.C7
import L11.C8
import L11.C9
import L11.C10
import L11.C11
import L11.C12
import L11.C13
import L11.C14
import L11.C15
import L11.C16
import L11.C17
import L11.C18
import L11.C19
import L11.C20
import L11.C21
import L11.C22
import L11.C23
import L11.C24
import L11.C25
import L11.C26
import L11.C27
import L11.C28
import L11.C29
import L11.C30
import L11.C31
import L11.C32
import L11.C33
import L11.C34
import L11.C35
import L11.C36
import L11.C37
import L11.C38
import L11.C39
import L11.C40
import L11.C41
import L11.C42
import L11.C43
import L11.C44
import L11.C45
import L11.C46
import L11.C47
import L11.C48
import L11.C49
import L11.C50
import L11.C51
import L11.C52
import L11.C53
import L11.C54
import L11.C55
import L11.C56
import L11.C57
import L11.C58
import L11.C59
import L11.C60
import L11.C61
import L11.C62
import L11.C63
open LebesgueCover LebesgueCover.Cert LebesgueCover.Fast
namespace L11
/-- The vertex table of the certificate (kernel-checked enclosures). -/
theorem hV : VertTableOK ns11 VQ (mkRat 1 (2 ^ 36)) := vertTable_ok (by decide)
/-- **The root box of the 11D certificate is good**: every placement in it has hull area > 0.8366. -/
theorem root11_good : GoodBox ns11 tau11 (fun i => rl11.getD i 0) (fun i => rh11.getD i 0) := by
  refine root_good' (d := 11) (e := 1) (B := 1) (J := 2048) (fun j hj => ?_) (by norm_num)
  obtain ⟨k, hk⟩ : ∃ k, k = j / 32 := ⟨_, rfl⟩
  have hk2 : k < 64 := by omega
  interval_cases k
  · exact L11.C0.good hV j (by omega) (by omega)
  · exact L11.C1.good hV j (by omega) (by omega)
  · exact L11.C2.good hV j (by omega) (by omega)
  · exact L11.C3.good hV j (by omega) (by omega)
  · exact L11.C4.good hV j (by omega) (by omega)
  · exact L11.C5.good hV j (by omega) (by omega)
  · exact L11.C6.good hV j (by omega) (by omega)
  · exact L11.C7.good hV j (by omega) (by omega)
  · exact L11.C8.good hV j (by omega) (by omega)
  · exact L11.C9.good hV j (by omega) (by omega)
  · exact L11.C10.good hV j (by omega) (by omega)
  · exact L11.C11.good hV j (by omega) (by omega)
  · exact L11.C12.good hV j (by omega) (by omega)
  · exact L11.C13.good hV j (by omega) (by omega)
  · exact L11.C14.good hV j (by omega) (by omega)
  · exact L11.C15.good hV j (by omega) (by omega)
  · exact L11.C16.good hV j (by omega) (by omega)
  · exact L11.C17.good hV j (by omega) (by omega)
  · exact L11.C18.good hV j (by omega) (by omega)
  · exact L11.C19.good hV j (by omega) (by omega)
  · exact L11.C20.good hV j (by omega) (by omega)
  · exact L11.C21.good hV j (by omega) (by omega)
  · exact L11.C22.good hV j (by omega) (by omega)
  · exact L11.C23.good hV j (by omega) (by omega)
  · exact L11.C24.good hV j (by omega) (by omega)
  · exact L11.C25.good hV j (by omega) (by omega)
  · exact L11.C26.good hV j (by omega) (by omega)
  · exact L11.C27.good hV j (by omega) (by omega)
  · exact L11.C28.good hV j (by omega) (by omega)
  · exact L11.C29.good hV j (by omega) (by omega)
  · exact L11.C30.good hV j (by omega) (by omega)
  · exact L11.C31.good hV j (by omega) (by omega)
  · exact L11.C32.good hV j (by omega) (by omega)
  · exact L11.C33.good hV j (by omega) (by omega)
  · exact L11.C34.good hV j (by omega) (by omega)
  · exact L11.C35.good hV j (by omega) (by omega)
  · exact L11.C36.good hV j (by omega) (by omega)
  · exact L11.C37.good hV j (by omega) (by omega)
  · exact L11.C38.good hV j (by omega) (by omega)
  · exact L11.C39.good hV j (by omega) (by omega)
  · exact L11.C40.good hV j (by omega) (by omega)
  · exact L11.C41.good hV j (by omega) (by omega)
  · exact L11.C42.good hV j (by omega) (by omega)
  · exact L11.C43.good hV j (by omega) (by omega)
  · exact L11.C44.good hV j (by omega) (by omega)
  · exact L11.C45.good hV j (by omega) (by omega)
  · exact L11.C46.good hV j (by omega) (by omega)
  · exact L11.C47.good hV j (by omega) (by omega)
  · exact L11.C48.good hV j (by omega) (by omega)
  · exact L11.C49.good hV j (by omega) (by omega)
  · exact L11.C50.good hV j (by omega) (by omega)
  · exact L11.C51.good hV j (by omega) (by omega)
  · exact L11.C52.good hV j (by omega) (by omega)
  · exact L11.C53.good hV j (by omega) (by omega)
  · exact L11.C54.good hV j (by omega) (by omega)
  · exact L11.C55.good hV j (by omega) (by omega)
  · exact L11.C56.good hV j (by omega) (by omega)
  · exact L11.C57.good hV j (by omega) (by omega)
  · exact L11.C58.good hV j (by omega) (by omega)
  · exact L11.C59.good hV j (by omega) (by omega)
  · exact L11.C60.good hV j (by omega) (by omega)
  · exact L11.C61.good hV j (by omega) (by omega)
  · exact L11.C62.good hV j (by omega) (by omega)
  · exact L11.C63.good hV j (by omega) (by omega)
/-- **Theorem 1.1 (third bound):** `M(D, B₃, B₅, B₇, B₉) ≥ 0.8366`. -/
theorem hull5_ge : Hull5Statement := hull5_of_root_good root11_good
/-- `Λ ≥ 0.8366` for weak universal covers (convex sets of diameter exactly 1, reflections allowed). -/
theorem weak_main5 : WeakMain5Statement := weak5_of_hull5 hull5_ge
/-- `Λ ≥ 0.8366`. -/
theorem main5 : Main5Statement := main5_of_hull5 hull5_ge
/-- Consequently `Λ ≥ 0.836` (both readings), the earlier bound. -/
theorem weak_main_836 : WeakMainStatement := weak_of_weak5 weak_main5
theorem main_836 : MainStatement := main_of_main5 main5
end L11
