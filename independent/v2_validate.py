"""Validation of v1_leafcheck.py on a few leaves.
(a) F_min (exact box minimum of the fan area) vs brute force: random points (direct shoelace) and vertices x fine rho grid;
(b) pair_min vs brute force on random pairs;
(c) coefficient formula vs direct shoelace at random points;
(d) negative tests: the leaf containing Mishra's optimum must fail at tau = 0.8348 and pass at 0.8347.
Usage: python -I v2_validate.py LEAVES.npz CENTRE_AREAS.npy   (outputs of t1_tree.py and h2_minsearch.py)
"""
import sys, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import v1_leafcheck as V
from flint import arb

lv = np.load(sys.argv[1])
vals = np.load(sys.argv[2])
rng = np.random.default_rng(5)
lo, hi = lv['lo'], lv['hi']
opt = np.array([-0.012149, 0.0, 0.0, 0.023, 0.0])
inside = np.nonzero(np.all((lo <= opt) & (opt <= hi), axis=1))[0]
print('leaves containing the optimum', inside.tolist())
test = [int(np.argmin(vals)), int(inside[0]), int(np.argsort(vals)[1000]), int(rng.integers(len(lo)))]


def Fdirect_f(W, p):
    cr, sr = math.cos(p[2]), math.sin(p[2])
    def X(b, q):
        if b == 2: return (cr * q[0] - sr * q[1] + p[3], sr * q[0] + cr * q[1] + p[4])
        if b == 1: return (q[0] + p[0], q[1] + p[1])
        return q
    Xs = [X(b, q) for b, q in W]
    return 0.5 * sum(Xs[j][0] * Xs[(j + 1) % len(Xs)][1] - Xs[j][1] * Xs[(j + 1) % len(Xs)][0] for j in range(len(Xs)))


for i in test:
    l, h = list(lo[i]), list(hi[i]); c = [0.5 * (a + b) for a, b in zip(l, h)]
    Wf = V.witnesses(c)
    W = [(b, (arb(q[0]), arb(q[1]))) for b, q in Wf]
    L = V.Leaf(l, h)
    Fmin = L.area_min(W)
    # (c) coefficient formula at random points vs direct
    C0, C1, C2, U, Vv, m = L.coef
    worst_c = 0.0
    for _ in range(5):
        p = [a + rng.uniform() * (b - a) for a, b in zip(l, h)]
        t3 = (arb(p[0]), arb(p[1])); t5 = (arb(p[3]), arb(p[4])); r = arb(p[2])
        Fc = (C0 + C1 * r.cos() + C2 * r.sin() + V.det(U[1], t3) + V.det(U[2], t5)
              + V.det((Vv[1][0] * r.cos() - Vv[1][1] * r.sin(), Vv[1][0] * r.sin() + Vv[1][1] * r.cos()), t3)
              + V.det((Vv[2][0] * r.cos() - Vv[2][1] * r.sin(), Vv[2][0] * r.sin() + Vv[2][1] * r.cos()), t5)
              + m * V.det(t3, t5)) / 2
        worst_c = max(worst_c, abs(float(Fc.mid()) - Fdirect_f(Wf, p)))
    # (a) brute force
    rnd = min(Fdirect_f(Wf, [a + rng.uniform() * (b - a) for a, b in zip(l, h)]) for _ in range(300))
    grid = 1e9
    for s in range(16):
        bits = [(s >> b) & 1 for b in range(4)]
        for rr in np.linspace(l[2], h[2], 401):
            p = [l[0] if bits[0] == 0 else h[0], l[1] if bits[1] == 0 else h[1], rr, l[3] if bits[2] == 0 else h[3], l[4] if bits[3] == 0 else h[4]]
            grid = min(grid, Fdirect_f(Wf, p))
    # (b) pair_min vs brute force on 30 random consecutive pairs
    worst_p = 0.0; viol = 0
    for _ in range(30):
        j = int(rng.integers(len(W))); b1, q1 = W[j]; b2, q2 = W[(j + 1) % len(W)]
        pm = float(L.pair_min(b1, q1, b2, q2, (arb(0), arb(0))).mid())
        bf = 1e9
        for _k in range(200):
            p = [a + rng.uniform() * (b - a) for a, b in zip(l, h)]
            cr, sr = math.cos(p[2]), math.sin(p[2])
            def X(b, q):
                if b == 2: return (cr * q[0] - sr * q[1] + p[3], sr * q[0] + cr * q[1] + p[4])
                if b == 1: return (q[0] + p[0], q[1] + p[1])
                return q
            x, y = X(*Wf[j]), X(*Wf[(j + 1) % len(Wf)])
            bf = min(bf, x[0] * y[1] - x[1] * y[0])
        if bf < pm - 1e-15: viol += 1
        worst_p = max(worst_p, bf - pm)
    print(f'leaf {i}: wit {len(W)}; F_min {Fmin.str(12)}; brute random-min {rnd:.12f}; vertex x rho-grid min {grid:.12f}; '
          f'coef-vs-direct {worst_c:.1e}; pair_min violations {viol}, max(brute - pair_min) {worst_p:.2e}', flush=True)

i = int(inside[0])
for tau in ('0.8347', '0.8348', '0.83478'):
    ok, msg = V.check_box(list(lo[i]), list(hi[i]), arb(tau), 0, {})
    print(f'optimum leaf {i} at tau {tau}: ok={ok} {msg}', flush=True)
