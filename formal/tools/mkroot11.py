"""Chunk files L11/C<k>.lean (32 consecutive cells each, from the per-cell G<ci> lemmas) and the final
L11/Root11Good.lean: GoodBox of the root box, Hull5Statement, WeakMain5Statement, Main5Statement.
usage: mkroot11.py LEANDIR"""
import sys, os
od = os.path.join(sys.argv[1], 'L11'); os.makedirs(od, exist_ok=True)
NC, CH = 2048, 32
HDR = ["open LebesgueCover LebesgueCover.Cert LebesgueCover.Fast"]
def P(j): return (f'∀ c ∈ ((gridCells (gridSplits 11 1) rl11 rh11).drop ({j} * 1)).take 1,\n'
                  f'      GoodBox ns11 tau11 (fun i => c.1.getD i 0) (fun i => c.2.getD i 0)')
for k in range(NC // CH):
    a, b = k*CH, (k + 1)*CH
    L = ['import LebesgueCover.TreeSound'] + [f'import L11.G{ci}' for ci in range(a, b)] + HDR + [f'namespace L11.C{k}',
         'theorem good (hV : VertTableOK ns11 VQ (mkRat 1 (2 ^ 36))) (j : ℕ) (h1 : ' + str(a) + ' ≤ j) (h2 : j < ' + str(b) + ') :',
         '    ' + P('j') + ' := by',
         '  interval_cases j'] + [f'  · exact L11.G{ci}.good hV' for ci in range(a, b)] + [f'end L11.C{k}']
    open(os.path.join(od, f'C{k}.lean'), 'w').write('\n'.join(L) + '\n')
nk = NC // CH
L = (['import LebesgueCover.Main5', 'import LebesgueCover.Diam'] + [f'import L11.C{k}' for k in range(nk)] + HDR +
     ['namespace L11',
      '/-- The vertex table of the certificate (kernel-checked enclosures). -/',
      'theorem hV : VertTableOK ns11 VQ (mkRat 1 (2 ^ 36)) := vertTable_ok (by decide)',
      '/-- **The root box of the 11D certificate is good**: every placement in it has hull area > 0.8366. -/',
      'theorem root11_good : GoodBox ns11 tau11 (fun i => rl11.getD i 0) (fun i => rh11.getD i 0) := by',
      f'  refine root_good\' (d := 11) (e := 1) (B := 1) (J := {NC}) (fun j hj => ?_) (by norm_num)',
      f'  obtain ⟨k, hk⟩ : ∃ k, k = j / {CH} := ⟨_, rfl⟩',
      f'  have hk2 : k < {nk} := by omega',
      '  interval_cases k'] +
     [f'  · exact L11.C{k}.good hV j (by omega) (by omega)' for k in range(nk)] +
     ['/-- **Theorem 1.1 (third bound):** `M(D, B₃, B₅, B₇, B₉) ≥ 0.8366`. -/',
      'theorem hull5_ge : Hull5Statement := hull5_of_root_good root11_good',
      '/-- `Λ ≥ 0.8366` for weak universal covers (convex sets of diameter exactly 1, reflections allowed). -/',
      'theorem weak_main5 : WeakMain5Statement := weak5_of_hull5 hull5_ge',
      '/-- `Λ ≥ 0.8366`. -/',
      'theorem main5 : Main5Statement := main5_of_hull5 hull5_ge',
      '/-- Consequently `Λ ≥ 0.836` (both readings), the earlier bound. -/',
      'theorem weak_main_836 : WeakMainStatement := weak_of_weak5 weak_main5',
      'theorem main_836 : MainStatement := main_of_main5 main5',
      'end L11'])
open(os.path.join(od, 'Root11Good.lean'), 'w').write('\n'.join(L) + '\n')
print('chunks', nk)
