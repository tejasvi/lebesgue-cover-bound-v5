"""gen11 (audit): independent float geometry for D u (B3 + t1) u (R(r2) B5 + t2) u (R(r3) B7 + t3) u (R(r4) B9 + t4)
(parameter layout of the 11D certificate: p = [t1x, t1y, r2, t2x, t2y, r3, t3x, t3y, r4, t4x, t4y]).
Generalises audit8/gen8.py (same method, written for the 8D audit) to four bodies:
  area(p):         exact hull area via the support function (exact per-body pieces, closed-form crossings and integrals)
  poly_bounds(p):  inner polygon hull of boundary samples + Steiner outer bound (two-sided check of area)
  witnesses(p):    ordered support points of the exact hull (arcs subdivided to sagitta <= eps), as (body, material q)
Bodies: 0 = disk (radius 1/2), 1 = B3 (rotation 0), 2 = B5, 3 = B7, 4 = B9; regular Reuleaux n-gon of width 1 with
corners R_n (cos 2 pi l/n, sin 2 pi l/n), R_n = 1/(2 cos(pi/(2n)))."""
import math
import numpy as np
TWO_PI = 2 * math.pi
NS = (3, 5, 7, 9)


def placements(p):
    return [(3, 0.0, (p[0], p[1])), (5, p[2], (p[3], p[4])), (7, p[5], (p[6], p[7])), (9, p[8], (p[9], p[10]))]


def pieces(p):
    out = [[(0.0, TWO_PI, 0.0, 0.0, 0.5, 0, None)]]
    for bi, (n, r_, t_) in enumerate(placements(p), start=1):
        R = 1 / (2 * math.cos(math.pi / (2 * n))); pcs = []
        for l in range(n):
            ph = r_ + TWO_PI * l / n
            vx, vy = R * math.cos(ph) + t_[0], R * math.sin(ph) + t_[1]
            pcs.append((ph - math.pi / (2 * n), ph + math.pi / (2 * n), vx, vy, 0.0, bi, l))
            pcs.append((ph + math.pi - math.pi / (2 * n), ph + math.pi + math.pi / (2 * n), vx, vy, 1.0, bi, l))
        out.append(pcs)
    return out


def piece_at(pcs, th):
    for pc in pcs:
        if (th - pc[0]) % TWO_PI <= (pc[1] - pc[0]) + 1e-12: return pc
    raise RuntimeError('no piece')


def hull_intervals(p):
    bodies = pieces(p)
    brk = sorted({x % TWO_PI for pcs in bodies for pc in pcs for x in (pc[0], pc[1])})
    brk = [0.0] + [x for x in brk if x > 0] + [TWO_PI]
    out = []
    nb = len(bodies)
    for k in range(len(brk) - 1):
        a0, a1 = brk[k], brk[k + 1]
        if a1 - a0 <= 1e-13: continue
        fs = [piece_at(pcs, 0.5 * (a0 + a1)) for pcs in bodies]
        cuts = [a0, a1]
        for i in range(nb):
            for j in range(i + 1, nb):
                A, B, C = fs[i][2] - fs[j][2], fs[i][3] - fs[j][3], fs[j][4] - fs[i][4]
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
            if c1 - c0 <= 1e-13: continue
            cm = 0.5 * (c0 + c1)
            out.append((c0, c1, max(fs, key=lambda f: f[2] * math.cos(cm) + f[3] * math.sin(cm) + f[4])))
    return out


def _G(a, b, r, th):
    return (a * a - b * b) * math.sin(2 * th) / 2 - a * b * math.cos(2 * th) + 2 * r * (a * math.sin(th) - b * math.cos(th)) + r * r * th


def area(p):
    return 0.5 * sum(_G(pc[2], pc[3], pc[4], c1) - _G(pc[2], pc[3], pc[4], c0) for (c0, c1, pc) in hull_intervals(p))


def poly_bounds(p, K=4096):
    from scipy.spatial import ConvexHull
    th = np.linspace(0, TWO_PI, 8 * K, endpoint=False)
    pts = [0.5 * np.column_stack([np.cos(th), np.sin(th)])]
    smax = 0.5 * (1 - math.cos(math.pi / (8 * K)))
    for (n, r_, t_) in placements(p):
        R = 1 / (2 * math.cos(math.pi / (2 * n)))
        for l in range(n):
            ph = r_ + TWO_PI * l / n
            V = np.array([R * math.cos(ph) + t_[0], R * math.sin(ph) + t_[1]])
            a = np.linspace(ph + math.pi - math.pi / (2 * n), ph + math.pi + math.pi / (2 * n), K + 1)
            pts.append(V + np.column_stack([np.cos(a), np.sin(a)]))
        smax = max(smax, 1 - math.cos(math.pi / n / K / 2))
    P = np.vstack(pts); h = ConvexHull(P)
    return h.volume, h.volume + h.area * smax + math.pi * smax * smax


def witnesses(p, eps=1e-8, shrink=1.0 - 2.0 ** -44):
    pl = placements(p)
    W = []
    for (c0, c1, pc) in hull_intervals(p):
        a, b, r, bi = pc[2], pc[3], pc[4], pc[5]
        if r == 0.0: ths = [0.5 * (c0 + c1)]
        else:
            dmax = 2 * math.sqrt(2 * eps / r)
            k = max(1, int(math.ceil((c1 - c0) / dmax)))
            ths = [c0 + (c1 - c0) * s / k for s in range(k + 1)]
        for th in ths:
            x = (a + r * math.cos(th), b + r * math.sin(th))
            if bi == 0: q = x
            else:
                n, rho, t = pl[bi - 1]; y = (x[0] - t[0], x[1] - t[1]); cr, sr = math.cos(rho), math.sin(rho)
                q = (cr * y[0] + sr * y[1], -sr * y[0] + cr * y[1])
            q = (q[0] * shrink, q[1] * shrink)
            if W and W[-1][0] == bi and abs(W[-1][1][0] - q[0]) + abs(W[-1][1][1] - q[1]) < 1e-15: continue
            W.append((bi, q))
    if len(W) > 1 and W[0][0] == W[-1][0] and abs(W[0][1][0] - W[-1][1][0]) + abs(W[0][1][1] - W[-1][1][1]) < 1e-15: W.pop()
    return W


if __name__ == '__main__':
    rng = np.random.default_rng(1)
    for _ in range(8):
        p = [rng.uniform(-0.15, 0.15), rng.uniform(-0.15, 0.15), rng.uniform(0, 0.63), rng.uniform(-0.15, 0.15), rng.uniform(-0.15, 0.15),
             rng.uniform(0, 0.9), rng.uniform(-0.15, 0.15), rng.uniform(-0.15, 0.15), rng.uniform(0, 0.7), rng.uniform(-0.15, 0.15),
             rng.uniform(-0.15, 0.15)]
        a = area(p); lo, hi = poly_bounds(p, 8192)
        print(f'exact {a:.12f}  poly [{lo:.12f}, {hi:.12f}]  inside: {lo - 1e-12 <= a <= hi + 1e-12}')
