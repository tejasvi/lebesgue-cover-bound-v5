"""test_area.py: area_min (exact vertex/rotation method) against brute force: at each of the 256 translation vertices,
multi-start L-BFGS-B over the three rotations on the float fan area."""
import sys, os, math, itertools, time
sys.dont_write_bytecode = True
import numpy as np
from scipy.optimize import minimize
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import v11_leafcheck as V
rng = np.random.default_rng(5)
p0 = np.array([0.0378, -0.0441, 0.1178, 0.0127, 0.0063, 0.2805, -0.0126, 0.0189, 0.2182, -0.0063, -0.0157])
for hw in ([0.004] * 11, [0.01, 0.005, 0.04, 0.01, 0.005, 0.05, 0.01, 0.005, 0.045, 0.005, 0.005]):
    lo = list(p0 - np.array(hw)); hi = list(p0 + np.array(hw))
    bx = V.Box(lo, hi); st = {}
    W, msg = V.fan_for(bx, V.wit_arb(bx.c, 1e-8), st); assert W is not None, msg
    t0 = time.time(); V.TSTAT['fallback'] = 0
    am = V.area_min(bx, V.coefs(W)); ta = time.time() - t0
    b_ = np.array([b for b, q in W]); Q = np.array([[float(q[0].mid()), float(q[1].mid())] for b, q in W])
    def F(p):
        X = Q.copy()
        for b, (ix, iy) in V.TR.items():
            m = b_ == b; r = p[V.ROT[b]] if b in V.ROT else 0.0; c, s = math.cos(r), math.sin(r)
            X[m] = Q[m] @ np.array([[c, s], [-s, c]]) + np.array([p[ix], p[iy]])
        Xn = np.roll(X, -1, axis=0)
        return 0.5 * float(np.sum(X[:, 0] * Xn[:, 1] - X[:, 1] * Xn[:, 0]))
    best = math.inf; t0 = time.time()
    for combo in itertools.product((0, 1), repeat=8):
        p = np.array(bx.c)
        for k, (b, (ix, iy)) in enumerate(V.TR.items()):
            p[ix] = lo[ix] if combo[2 * k] == 0 else hi[ix]; p[iy] = lo[iy] if combo[2 * k + 1] == 0 else hi[iy]
        rb = [(lo[V.ROT[b]], hi[V.ROT[b]]) for b in V.RB]
        def g(x):
            pp = p.copy()
            for b, v in zip(V.RB, x): pp[V.ROT[b]] = v
            return F(pp)
        for x0 in itertools.product(*rb):
            r = minimize(g, x0, method='L-BFGS-B', bounds=rb, options=dict(ftol=1e-15, gtol=1e-12)); best = min(best, r.fun)
        r = minimize(g, [0.5 * (a + b) for a, b in rb], method='L-BFGS-B', bounds=rb, options=dict(ftol=1e-15, gtol=1e-12)); best = min(best, r.fun)
    print(f'half-widths {hw[:3]}...: area_min {am.str(15)} ({ta:.1f} s, {V.TSTAT["fallback"]} fallbacks), brute force {best:.15f} ({time.time() - t0:.0f} s), '
          f'gap {best - float(am.lower()):.3e}, witnesses {len(W)}, drops {st.get("drops", 0)}')
    assert float(am.lower()) <= best + 1e-12
