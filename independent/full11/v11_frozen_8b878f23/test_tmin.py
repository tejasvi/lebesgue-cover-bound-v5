"""test_tmin.py: tmin against a multi-start local optimiser (scipy L-BFGS-B) on random 3-rotation trig polynomials."""
import sys, os, math
sys.dont_write_bytecode = True
import numpy as np
from scipy.optimize import minimize
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import v11_leafcheck as V
from flint import arb
rng = np.random.default_rng(11)
def mk():
    sc = 10 ** rng.uniform(-3, 0)
    return (arb(rng.normal()), {b: arb(rng.normal() * sc) for b in V.RB}, {b: arb(rng.normal() * sc) for b in V.RB},
            {pr: arb(rng.normal() * sc) for pr in V.PAIRS}, {pr: arb(rng.normal() * sc) for pr in V.PAIRS})
def ff(f, x):
    K, A, B, C, S = f; r = dict(zip(V.RB, x)); v = float(K.mid())
    for b in A: v += float(A[b].mid()) * math.cos(r[b]) + float(B[b].mid()) * math.sin(r[b])
    for (a, c) in C: v += float(C[(a, c)].mid()) * math.cos(r[c] - r[a]) + float(S[(a, c)].mid()) * math.sin(r[c] - r[a])
    return v
worst = 0.0; above = 0; n = 0; import time; t0 = time.time()
for trial in range(int(sys.argv[1]) if len(sys.argv) > 1 else 200):
    f = mk(); I = {}
    wmax = float(sys.argv[2]) if len(sys.argv) > 2 else 0.25
    for b in V.RB:
        a = rng.uniform(-3, 3); w = wmax * 10 ** rng.uniform(-2, 0); I[b] = (a, a + w)
    V.TSTAT['fallback'] = 0
    lb = float(V.tmin(f, I, V.Trig()).lower())
    bnds = [I[b] for b in V.RB]; best = math.inf
    for s in range(40):
        x0 = [rng.uniform(*I[b]) for b in V.RB]
        r = minimize(lambda x: ff(f, x), x0, method='L-BFGS-B', bounds=bnds, options=dict(ftol=1e-15, gtol=1e-13))
        best = min(best, r.fun)
    for x in np.array(np.meshgrid(*[I[b] for b in V.RB])).reshape(3, -1).T: best = min(best, ff(f, x))
    if lb > best + 1e-13: above += 1
    worst = max(worst, best - lb); n += 1
    if best - lb > 1e-9: print(f'  trial {trial}: gap {best - lb:.3e} widths {[round(I[b][1] - I[b][0], 4) for b in V.RB]} fallbacks {V.TSTAT["fallback"]}')
print(f'tmin vs optimiser: {n} polynomials (rotation widths <= {wmax}), bound above optimiser value: {above}, max gap {worst:.3e}, {time.time() - t0:.0f} s')
