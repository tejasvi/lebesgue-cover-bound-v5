"""Numerical attempts to break M(D,B3,B5) >= 0.8347 with an independent float hull-area code.
(1) float version of h1_hull.exact_area, validated against the mpmath version;
(2) area at every leaf centre and at random points of every leaf (necessary condition: all > tau);
(3) multistart Nelder-Mead over the root domain and refinement near Mishra's optimum.
Usage: python -I h2_minsearch.py LEAVES.npz NSTARTS SEED [CENTRE_AREAS_OUT.npy]
"""
import sys, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scipy.optimize import minimize
import h1_hull
import mpmath as mp

TWO_PI = 2 * math.pi


def body_pieces_f(p):
    t3 = (p[0], p[1]); rho = p[2]; t5 = (p[3], p[4])
    bodies = [[(0.0, TWO_PI, 0.0, 0.0, 0.5)]]
    for n, r_, t_ in ((3, 0.0, t3), (5, rho, t5)):
        R = 1 / (2 * math.cos(math.pi / (2 * n)))
        pcs = []
        for l in range(n):
            ph = r_ + TWO_PI * l / n
            vx, vy = R * math.cos(ph) + t_[0], R * math.sin(ph) + t_[1]
            pcs.append((ph - math.pi / (2 * n), ph + math.pi / (2 * n), vx, vy, 0.0))
            pcs.append((ph + math.pi - math.pi / (2 * n), ph + math.pi + math.pi / (2 * n), vx, vy, 1.0))
        bodies.append(pcs)
    return bodies


def G(c, th):
    a, b, r = c
    return (a * a - b * b) * math.sin(2 * th) / 2 - a * b * math.cos(2 * th) + 2 * r * (a * math.sin(th) - b * math.cos(th)) + r * r * th


def piece_at(pcs, th):
    for (s0, s1, a, b, r) in pcs:
        if (th - s0) % TWO_PI <= (s1 - s0) + 1e-12: return (a, b, r)
    raise RuntimeError


def area(p):
    bodies = body_pieces_f(p)
    brk = sorted({x % TWO_PI for pcs in bodies for (s0, s1, *_rest) in pcs for x in (s0, s1)})
    brk = [0.0] + [x for x in brk if x > 0] + [TWO_PI]
    tot = 0.0
    for k in range(len(brk) - 1):
        a0, a1 = brk[k], brk[k + 1]
        if a1 - a0 <= 1e-13: continue   # rounding slivers between adjacent pieces
        mid = 0.5 * (a0 + a1)
        fs = [piece_at(pcs, mid) for pcs in bodies]
        cuts = [a0, a1]
        for i in range(3):
            for j in range(i + 1, 3):
                A, B, C = fs[i][0] - fs[j][0], fs[i][1] - fs[j][1], fs[j][2] - fs[i][2]
                rr = math.hypot(A, B)
                if rr == 0 or abs(C) > rr: continue
                base = math.atan2(B, A); dl = math.acos(C / rr)
                for x0 in (base + dl, base - dl):
                    for m in (-2, -1, 0, 1, 2):
                        x = x0 + TWO_PI * m
                        if a0 < x < a1: cuts.append(x)
        cuts.sort()
        for u in range(len(cuts) - 1):
            c0, c1 = cuts[u], cuts[u + 1]
            if c1 <= c0: continue
            cm = 0.5 * (c0 + c1)
            best = max(fs, key=lambda f: f[0] * math.cos(cm) + f[1] * math.sin(cm) + f[2])
            tot += G(best, c1) - G(best, c0)
    return 0.5 * tot


if __name__ == '__main__':
    leaves = np.load(sys.argv[1], allow_pickle=False)
    nst = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]))
    lo, hi = leaves['lo'], leaves['hi']
    # (1) validation
    worst = 0.0
    for k in range(40):
        p = list(lo[0] * 0 + rng.uniform(-0.19, 0.19, 5)); p[2] = rng.uniform(0, 1.3)
        e, _ = h1_hull.exact_area(p, prec=25)
        worst = max(worst, abs(float(e) - area(p)))
    print(f'(1) float vs mpmath exact area, 40 random placements: max diff {worst:.2e}', flush=True)
    # (2) leaf centres and random points
    tau = 0.8347
    c = 0.5 * (lo + hi)
    vals = np.array([area(list(x)) for x in c])
    i0 = int(np.argmin(vals))
    print(f'(2) min area over {len(c)} leaf centres = {vals[i0]:.10f} at {np.round(c[i0], 6).tolist()}; # below tau: {(vals <= tau).sum()}', flush=True)
    rp = lo + rng.uniform(0, 1, size=(len(lo), 5)) * (hi - lo)
    vr = np.array([area(list(x)) for x in rp])
    j0 = int(np.argmin(vr))
    print(f'    min area over one random point per leaf = {vr[j0]:.10f} at {np.round(rp[j0], 6).tolist()}; # below tau: {(vr <= tau).sum()}', flush=True)
    corners_min = 1e9
    order = np.argsort(vals)[:400]
    for k in order:
        for s in range(32):
            bits = [(s >> b) & 1 for b in range(5)]
            x = [lo[k][d] if bits[d] == 0 else hi[k][d] for d in range(5)]
            corners_min = min(corners_min, area(x))
    print(f'    min over all 32 corners of the 400 leaves with smallest centre area = {corners_min:.10f}', flush=True)
    np.save(sys.argv[4] if len(sys.argv) > 4 else 'leaf_center_areas.npy', vals)
    # (3) multistart
    L0 = np.array([-0.1936, -0.1936, 0.0, -0.1968, -0.1968]); H0 = np.array([0.1936, 0.1936, math.pi / 5, 0.1968, 0.1968])
    best = (9, None)
    starts = [np.array([-0.01216, 0.0, 0.0, 0.02300, 0.0]), np.array([-0.01216, 0.0, 2 * math.pi / 5, 0.02300, 0.0])]
    starts += [L0 + rng.uniform(0, 1, 5) * (H0 - L0) for _ in range(nst)]
    starts += [c[i] for i in np.argsort(vals)[:20]]
    for k, x0 in enumerate(starts):
        r = minimize(lambda x: area(list(x)), x0, method='Nelder-Mead', options={'xatol': 1e-10, 'fatol': 1e-13, 'maxiter': 6000, 'adaptive': True})
        if r.fun < best[0]:
            best = (r.fun, r.x)
            print(f'    start {k}: {r.fun:.10f} at {np.round(r.x, 6).tolist()}', flush=True)
    print(f'(3) best local minimum found: {best[0]:.10f} at {np.round(best[1], 7).tolist()}')
    e, _ = h1_hull.exact_area(list(best[1]), prec=30)
    print(f'    mpmath exact area there: {mp.nstr(e, 14)}')
