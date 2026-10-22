"""test_v11.py: self-tests of v11_leafcheck (tmin exactness, area coefficients, box minima vs sampling, negative cases)."""
import sys, os, math, itertools
sys.dont_write_bytecode = True
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import v11_leafcheck as V
import gen11
from flint import arb
rng = np.random.default_rng(7)

def f_float(f, r):
    K, A, B, C, S = f
    v = float(K.mid())
    for b in A: v += float(A[b].mid()) * math.cos(r[b]) + float(B[b].mid()) * math.sin(r[b])
    for (x, y) in C: v += float(C[(x, y)].mid()) * math.cos(r[y] - r[x]) + float(S[(x, y)].mid()) * math.sin(r[y] - r[x])
    return v

# 1. tmin vs dense grid
worst = 0.0; nt = 0
for trial in range(300):
    sc = 10 ** rng.uniform(-3, 0)
    K = arb(rng.normal()); A = {b: arb(rng.normal() * sc) for b in V.RB}; B = {b: arb(rng.normal() * sc) for b in V.RB}
    C = {pr: arb(rng.normal() * sc) for pr in V.PAIRS}; S = {pr: arb(rng.normal() * sc) for pr in V.PAIRS}
    I = {}
    for b in V.RB:
        a = rng.uniform(-3, 3); w = 10 ** rng.uniform(-3, 0.2); I[b] = (a, a + w)
    f = (K, A, B, C, S)
    cs = V.Trig(); lb = V.tmin(f, I, cs)
    G = 13; grids = {b: np.linspace(I[b][0], I[b][1], G) for b in V.RB}
    gmin = min(f_float(f, dict(zip(V.RB, pt))) for pt in itertools.product(*[grids[b] for b in V.RB]))
    # refine around the grid minimiser with a local random search
    best = gmin
    for _ in range(3000):
        pt = {b: rng.uniform(*I[b]) for b in V.RB}; best = min(best, f_float(f, pt))
    lbf = float(lb.lower())
    assert lbf <= best + 1e-12, ('tmin above a sampled value', trial, lbf, best)
    worst = max(worst, best - lbf); nt += 1
print(f'1. tmin: {nt} random 3-rotation trig polynomials, lower bound <= every sampled value; max (sampled min - bound) = {worst:.3e}')

# 2/3/4. a real configuration near the optimum region
p0 = [0.0378, -0.0441, 0.1178, 0.0127, 0.0063, 0.2805, -0.0126, 0.0189, 0.2182, -0.0063, -0.0157]
W0 = V.wit_arb(p0, 1e-8)
co = V.coefs(W0)
def eval_co(co, p):
    T = {b: (p[ix], p[iy]) for b, (ix, iy) in V.TR.items()}
    d = lambda a, b: float(a[0].mid()) * b[1] - float(a[1].mid()) * b[0]
    K = float(co['C0'].mid()) + sum(d(co['U'][b], T[b]) for b in V.TR)
    K += sum(float(co['m'][(b, c)].mid()) * (T[b][0] * T[c][1] - T[b][1] * T[c][0]) for (b, c) in co['m'])
    v = K
    for r in V.RB:
        Ar = float(co['A0'][r].mid()) + sum(d(co['Vr'][(r, b)], T[b]) for b in V.TR)
        Br = float(co['B0'][r].mid()) + sum(d(V.J(co['Vr'][(r, b)]), T[b]) for b in V.TR)
        v += Ar * math.cos(p[V.ROT[r]]) + Br * math.sin(p[V.ROT[r]])
    for (x, y) in V.PAIRS:
        v += float(co['Cc'][(x, y)].mid()) * math.cos(p[V.ROT[y]] - p[V.ROT[x]]) + float(co['Sc'][(x, y)].mid()) * math.sin(p[V.ROT[y]] - p[V.ROT[x]])
    return v / 2
errs = []
for _ in range(20):
    p = list(np.array(p0) + rng.uniform(-0.02, 0.02, 11))
    errs.append(abs(eval_co(co, p) - V.fan_area_at(W0, p)))
print(f'2. coefficient form vs direct fan area at 20 points: max |diff| = {max(errs):.2e}; fan at p0 {V.fan_area_at(W0, p0):.12f}, exact hull {gen11.area(p0):.12f}, witnesses {len(W0)}')
assert max(errs) < 1e-12

for wscale in (1e-3, 1e-2):
    lo = list(np.array(p0) - wscale); hi = list(np.array(p0) + wscale)
    bx = V.Box(lo, hi); st = {}
    W, msg = V.fan_for(bx, V.wit_arb(bx.c, 1e-8), st)
    assert W is not None, msg
    zz = (arb(0), arb(0)); nW = len(W)
    assert all(bx.pair_min(W[j][0], W[j][1], W[(j + 1) % nW][0], W[(j + 1) % nW][1], zz) > 0 for j in range(nW)), 'final fan has a bad pair'
    amin_ = V.area_min(bx, V.coefs(W))
    samp = min(V.fan_area_at(W, list(np.where(rng.random(11) < 0.5, lo, hi)) if k < 500 else list(rng.uniform(lo, hi))) for k in range(1500))
    print(f'3. box half-width {wscale:g}: area_min {amin_.str(14)}, sampled min (vertices + interior) {samp:.14f}, gap {samp - float(amin_.lower()):.3e}, drops {st.get("drops", 0)}, fan {len(W)} witnesses')
    assert float(amin_.lower()) <= samp + 1e-13
    # pair minima vs sampling for the body-change pairs
    n = len(W); chk = 0; gapmax = 0.0
    z = (arb(0), arb(0))
    for j in range(n):
        b1, q1 = W[j]; b2, q2 = W[(j + 1) % n]
        if b1 == b2 and chk > 40: continue
        pm = float(bx.pair_min(b1, q1, b2, q2, z).lower())
        def dpt(p):
            X = []
            for b, q in ((b1, q1), (b2, q2)):
                if b == 0: X.append((float(q[0].mid()), float(q[1].mid()))); continue
                ix, iy = V.TR[b]; r = p[V.ROT[b]] if b in V.ROT else 0.0; c, s = math.cos(r), math.sin(r)
                X.append((c * float(q[0].mid()) - s * float(q[1].mid()) + p[ix], s * float(q[0].mid()) + c * float(q[1].mid()) + p[iy]))
            return X[0][0] * X[1][1] - X[0][1] * X[1][0]
        sm = min(dpt(list(np.where(rng.random(11) < 0.5, lo, hi)) if k < 200 else list(rng.uniform(lo, hi))) for k in range(400))
        assert pm <= sm + 1e-15, ('pair_min above sample', j, pm, sm)
        gapmax = max(gapmax, sm - pm); chk += 1
    print(f'4. pair minima on {chk} pairs (all body changes + 40 same-body): bound <= sampled min, max gap {gapmax:.2e}')

# 5. negative cases: reversed pair must have a negative minimum; a witness outside its body must fail membership
b1, q1 = W[3]; b2, q2 = W[4]
assert not (bx.pair_min(b2, q2, b1, q1, (arb(0), arb(0))) > 0)
qout = (arb(0.5) * 1.000001, arb(0)); assert not V.member(0, qout)
# a planted 1e-10 shortfall: tau = area_min + 1e-10 must fail the comparison, area_min - 1e-10 must pass
tau_hi = arb(float(amin_.lower()) + 1e-10); tau_lo = arb(float(amin_.lower()) - 1e-10)
assert not (amin_ > tau_hi) and (amin_ > tau_lo)
print('5. negative cases: reversed pair rejected, outside witness rejected, tau = bound +- 1e-10 resolved: OK')
