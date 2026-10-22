"""Numerical sanity checks of the reduction lemmas with the independent area code (h2_minsearch.area).
(1) f(g_n(T)) at the header half-widths (mpmath);  (2) f(d) = area conv(D u {x}) vs direct polygon hull;
(3) corner lemma: min over rotations of the max corner distance = g_n(|t|);  (4) far field: random placements with
|t_i| >= T_i have area >= f(g(|t_i|)) > tau;  (5) reflection and 2pi/5 periodicity of the area function."""
import sys, os, math
import numpy as np, mpmath as mp
from scipy.spatial import ConvexHull
if not __debug__:
    raise SystemExit('l1_lemmas.py uses assert statements; run it without -O')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from h2_minsearch import area
mp.mp.dps = 30
T3, T5 = mp.mpf(0.1936129927635193), mp.mpf(0.19685649871826172)
def f(d): return (mp.pi - mp.acos(1 / (2 * d))) / 4 + mp.sqrt(d * d - mp.mpf(1) / 4) / 2
def g(n, m):
    R = 1 / (2 * mp.cos(mp.pi / (2 * n))); return mp.sqrt(R * R + m * m + 2 * R * m * mp.cos(mp.pi / n))
print('(1) f(g_3(T3)) =', mp.nstr(f(g(3, T3)), 12), ' f(g_5(T5)) =', mp.nstr(f(g(5, T5)), 12), ' (must be > 0.8347)')
# (2)
th = np.linspace(0, 2 * np.pi, 200000, endpoint=False)
for d in (0.6, 0.7, 1.0):
    P = np.vstack([0.5 * np.column_stack([np.cos(th), np.sin(th)]), [[d, 0.0]]])
    print(f'(2) d={d}: f(d) = {float(f(mp.mpf(d))):.9f}, polygon hull = {ConvexHull(P).volume:.9f}')
# (3)
rng = np.random.default_rng(9)
worst = 0.0
for n in (3, 5):
    R = 1 / (2 * math.cos(math.pi / (2 * n)))
    for _ in range(2000):
        m = rng.uniform(0, 0.3); a = rng.uniform(0, 2 * math.pi)
        dmax = max(math.hypot(R * math.cos(a + 2 * math.pi * l / n) + m, R * math.sin(a + 2 * math.pi * l / n)) for l in range(n))
        worst = max(worst, float(g(n, mp.mpf(m))) - dmax)
print(f'(3) max over 4000 random (rho, t) of g_n(|t|) - max corner distance = {worst:.2e} (must be <= 0)')
# (4)
mn = 9.0
for _ in range(3000):
    p = [rng.uniform(-0.25, 0.25), rng.uniform(-0.25, 0.25), rng.uniform(0, 2 * math.pi), rng.uniform(-0.25, 0.25), rng.uniform(-0.25, 0.25)]
    m3, m5 = math.hypot(p[0], p[1]), math.hypot(p[3], p[4])
    if m3 < float(T3) and m5 < float(T5): continue
    A = area(p)
    lb = max(float(f(g(3, mp.mpf(m3)))) if m3 >= float(T3) else 0, float(f(g(5, mp.mpf(m5)))) if m5 >= float(T5) else 0)
    assert A >= lb - 1e-12, (p, A, lb)
    mn = min(mn, A)
print(f'(4) far-field placements: all areas >= corner bound; min area among them = {mn:.6f}')
# (5)
wr = 0.0; wp = 0.0
for _ in range(200):
    p = [rng.uniform(-0.2, 0.2), rng.uniform(-0.2, 0.2), rng.uniform(0, 2 * math.pi), rng.uniform(-0.2, 0.2), rng.uniform(-0.2, 0.2)]
    q = [p[0], -p[1], -p[2], p[3], -p[4]]
    wr = max(wr, abs(area(p) - area(q)))
    wp = max(wp, abs(area(p) - area([p[0], p[1], p[2] + 2 * math.pi / 5, p[3], p[4]])))
print(f'(5) reflection symmetry max diff {wr:.1e}; 2pi/5 periodicity max diff {wp:.1e}')
