"""Validation of v8_leafcheck.py: F_min vs brute force (random points; 64 vertices x rho5 x rho7 grid), coefficient
formula vs direct shoelace, pair_min vs brute force (all pair types incl. B5-B7 transitions).
Usage: python -I v8_validate.py LEAVES.npz   (LEAVES.npz from t1_tree.py)"""
import sys, os, math, itertools
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import v8_leafcheck as V, gen8
from flint import arb
lv = np.load(sys.argv[1])
lo, hi = lv['lo'], lv['hi']; vol = np.prod(hi - lo, axis=1)
rng = np.random.default_rng(8)
TRf = {1: (0, 1), 2: (3, 4), 3: (6, 7)}; ROTf = {2: 2, 3: 5}


def Xf(p, b, q):
    if b == 0: return q
    if b == 1: return (q[0] + p[0], q[1] + p[1])
    r = p[ROTf[b]]; cs, sn = math.cos(r), math.sin(r); ix, iy = TRf[b]
    return (cs * q[0] - sn * q[1] + p[ix], sn * q[0] + cs * q[1] + p[iy])


def Fd(W, p):
    X = [Xf(p, b, q) for b, q in W]
    return 0.5 * sum(X[j][0] * X[(j + 1) % len(X)][1] - X[j][1] * X[(j + 1) % len(X)][0] for j in range(len(X)))


for i in [int(np.argmin(vol)), int(rng.integers(len(lo))), int(np.argsort(vol)[100]), int(np.argmax(vol))]:
    l, h = list(lo[i]), list(hi[i]); c = [0.5 * (a + b) for a, b in zip(l, h)]
    Wf = gen8.witnesses(c); W = [(b, (arb(q[0]), arb(q[1]))) for b, q in Wf]
    bx = V.Box(l, h); Fmin = bx.area_min(W)
    C0, A0, B0, Cc, Sc, U, Vr, m = bx.coef
    worst = 0.0
    for _ in range(4):
        p = [a + rng.uniform() * (b - a) for a, b in zip(l, h)]
        T = {1: (arb(p[0]), arb(p[1])), 2: (arb(p[3]), arb(p[4])), 3: (arb(p[6]), arb(p[7]))}
        r5, r7 = arb(p[2]), arb(p[5])
        K = C0 + sum((V.det(U[b], T[b]) for b in (1, 2, 3)), arb(0)) + m[(1, 2)] * V.det(T[1], T[2]) + m[(1, 3)] * V.det(T[1], T[3]) + m[(2, 3)] * V.det(T[2], T[3])
        tot = K + Cc * (r7 - r5).cos() + Sc * (r7 - r5).sin()
        for r, ang in ((2, r5), (3, r7)):
            A = A0[r] + sum((V.det(Vr[(r, b)], T[b]) for b in (1, 2, 3)), arb(0)); B = B0[r] + sum((V.det(V.J(Vr[(r, b)]), T[b]) for b in (1, 2, 3)), arb(0))
            tot += A * ang.cos() + B * ang.sin()
        worst = max(worst, abs(float((tot / 2).mid()) - Fd(Wf, p)))
    rnd = min(Fd(Wf, [a + rng.uniform() * (b - a) for a, b in zip(l, h)]) for _ in range(200))
    grid = 1e9
    for bits in itertools.product((0, 1), repeat=6):
        for r5 in np.linspace(l[2], h[2], 9):
            for r7 in np.linspace(l[5], h[5], 9):
                tv = [l[k] if bits[j] == 0 else h[k] for j, k in enumerate((0, 1, 3, 4, 6, 7))]
                p = [tv[0], tv[1], r5, tv[2], tv[3], r7, tv[4], tv[5]]
                grid = min(grid, Fd(Wf, p))
    # pairs
    viol = 0; worst_gap = 0.0; types = set()
    idxs = list(range(len(W)))
    trans = [j for j in idxs if W[j][0] != W[(j + 1) % len(W)][0]]
    pick = trans + list(rng.choice(idxs, 15, replace=False))
    z = (arb(0), arb(0))
    for j in pick:
        b1, q1 = W[j]; b2, q2 = W[(j + 1) % len(W)]; types.add((b1, b2))
        pm = float(bx.pair_min(b1, q1, b2, q2, z).lower())
        bf = 1e9
        for _ in range(150):
            p = [a + rng.uniform() * (b - a) for a, b in zip(l, h)]
            x, y = Xf(p, *Wf[j]), Xf(p, *Wf[(j + 1) % len(Wf)])
            bf = min(bf, x[0] * y[1] - x[1] * y[0])
        if bf < pm - 1e-15: viol += 1
    print(f'leaf {i}: F_min.lower {float(Fmin.lower()):.10f}  brute random {rnd:.10f}  vertex x grid {grid:.10f}  '
          f'coef-vs-direct {worst:.1e}  pair types {sorted(types)}  pair violations {viol}', flush=True)
