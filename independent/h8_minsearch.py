"""Numerical attempts to break M(D,B3,B5,B7) >= 0.836 with the independent area code gen8.area.
mode 'centres': area at every leaf centre of LEAVES (slice START:STOP) -> npy;  mode 'opt': multistart Nelder-Mead.
Usage: python -I h8_minsearch.py centres LEAVES.npz START STOP OUT.npy | opt NSTART SEED"""
import sys, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen8
from scipy.optimize import minimize
if sys.argv[1] == 'centres':
    lv = np.load(sys.argv[2], allow_pickle=False); a, b = int(sys.argv[3]), int(sys.argv[4])
    c = 0.5 * (lv['lo'][a:b] + lv['hi'][a:b])
    np.save(sys.argv[5], np.array([gen8.area(list(x)) for x in c]))
else:
    nst = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]))
    L0 = np.array([-0.19, -0.19, 0, -0.19, -0.19, 0, -0.19, -0.19]); H0 = np.array([0.19, 0.19, math.pi / 5, 0.19, 0.19, 2 * math.pi / 7, 0.19, 0.19])
    best = (9, None)
    for k in range(nst):
        x0 = L0 + rng.uniform(0, 1, 8) * (H0 - L0)
        if k < nst // 2: x0 = x0 * np.array([0.3, 0.3, 1, 0.3, 0.3, 1, 0.3, 0.3])     # half of the starts near the centre
        r = minimize(lambda x: gen8.area(list(x)), x0, method='Nelder-Mead', options={'xatol': 1e-10, 'fatol': 1e-13, 'maxiter': 20000, 'adaptive': True})
        if r.fun < best[0]:
            best = (r.fun, r.x); print(f'start {k}: {r.fun:.10f} at {np.round(r.x, 6).tolist()}', flush=True)
    print(f'best {best[0]:.10f} at {np.round(best[1], 7).tolist()}')
