"""Independent hull areas for D u (B3 + t3) u (R_rho B5 + t5).

Bodies: D = disk radius 1/2 at 0; B_n = regular Reuleaux n-gon of width 1 = intersection of the unit disks centred at
the corners V_l = R_n (cos 2 pi l/n, sin 2 pi l/n), R_n = 1/(2 cos(pi/(2n))); its boundary arc centred at V_l has
outward normals theta in [phi_l + pi - pi/(2n), phi_l + pi + pi/(2n)] (phi_l = direction of V_l).
Two independent area evaluations:
  poly_bounds(p, K): inner = area of the hull of K boundary samples per arc/circle (points exactly on the boundary),
                     outer = inner + perimeter * s + pi s^2 (Steiner; s = max sagitta)  -> rigorous up to float rounding;
  exact_area(p):     support function h = max of candidate functions a cos t + b sin t + r on their normal ranges,
                     switching angles solved in closed form, area = 1/2 int (h^2 - h'^2) integrated in closed form (mpmath).
"""
import numpy as np
import mpmath as mp
from scipy.spatial import ConvexHull


def corners(n, rho=0.0, t=(0.0, 0.0)):
    R = 1.0 / (2 * np.cos(np.pi / (2 * n)))
    ang = rho + 2 * np.pi * np.arange(n) / n
    return np.column_stack([R * np.cos(ang) + t[0], R * np.sin(ang) + t[1]]), ang


def body_points(p, K):
    t3 = (p[0], p[1]); rho = p[2]; t5 = (p[3], p[4])
    th = np.linspace(0, 2 * np.pi, 8 * K, endpoint=False)
    pts = [0.5 * np.column_stack([np.cos(th), np.sin(th)])]
    for n, r_, t_ in ((3, 0.0, t3), (5, rho, t5)):
        V, ang = corners(n, r_, t_)
        for l in range(n):
            a = np.linspace(ang[l] + np.pi - np.pi / (2 * n), ang[l] + np.pi + np.pi / (2 * n), K + 1)
            pts.append(V[l] + np.column_stack([np.cos(a), np.sin(a)]))
    return np.vstack(pts)


def poly_bounds(p, K=4096):
    P = body_points(p, K)
    hull = ConvexHull(P)
    inner = hull.volume
    perim = hull.area
    # max angular step: disk 2pi/(8K) (radius 1/2), arcs (pi/n)/K (radius 1)
    s = max(0.5 * (1 - np.cos(np.pi / (8 * K))), 1 - np.cos(np.pi / (3 * K) / 2))
    return inner, inner + perim * s + np.pi * s * s


def body_pieces(p, prec=40):
    """support function of each body as an exact partition of [0, 2pi): list per body of (start, end, a, b, r)
    with h = a cos t + b sin t + r on [start, end] (angles reduced to [0, 2pi), pieces may wrap)."""
    mp.mp.dps = prec
    t3 = (mp.mpf(p[0]), mp.mpf(p[1])); rho = mp.mpf(p[2]); t5 = (mp.mpf(p[3]), mp.mpf(p[4]))
    bodies = [[(mp.mpf(0), 2 * mp.pi, mp.mpf(0), mp.mpf(0), mp.mpf(1) / 2)]]
    for n, r_, t_ in ((3, mp.mpf(0), t3), (5, rho, t5)):
        R = 1 / (2 * mp.cos(mp.pi / (2 * n)))
        pcs = []
        for l in range(n):
            ph = r_ + 2 * mp.pi * l / n
            vx, vy = R * mp.cos(ph) + t_[0], R * mp.sin(ph) + t_[1]
            pcs.append((ph - mp.pi / (2 * n), ph + mp.pi / (2 * n), vx, vy, mp.mpf(0)))           # corner cone
            pcs.append((ph + mp.pi - mp.pi / (2 * n), ph + mp.pi + mp.pi / (2 * n), vx, vy, mp.mpf(1)))  # arc
        bodies.append(pcs)
    return bodies


def _G(c, th):
    a, b, r = c
    return (a * a - b * b) * mp.sin(2 * th) / 2 - a * b * mp.cos(2 * th) + 2 * r * (a * mp.sin(th) - b * mp.cos(th)) + r * r * th


def _piece_at(pcs, th):
    for (s0, s1, a, b, r) in pcs:
        d = (th - s0) % (2 * mp.pi)
        if d <= (s1 - s0) + mp.mpf(10) ** (-(mp.mp.dps - 8)): return (a, b, r)
    raise RuntimeError('no piece')


def exact_area(p, prec=40):
    """exact (to working precision) area of the hull via the support function."""
    bodies = body_pieces(p, prec)
    brk = set()
    for pcs in bodies:
        for (s0, s1, a, b, r) in pcs:
            brk.add(s0 % (2 * mp.pi)); brk.add(s1 % (2 * mp.pi))
    brk = sorted(brk) + [2 * mp.pi]
    brk = [mp.mpf(0)] + [x for x in brk if x > 0]
    total = mp.mpf(0); nsub = 0
    for k in range(len(brk) - 1):
        a0, a1 = brk[k], brk[k + 1]
        if a1 - a0 <= mp.mpf(10) ** (-(mp.mp.dps - 6)): continue   # rounding slivers between adjacent pieces
        mid = (a0 + a1) / 2
        fs = [_piece_at(pcs, mid) for pcs in bodies]
        cuts = [a0, a1]
        for i in range(len(fs)):
            for j in range(i + 1, len(fs)):
                A, B, C = fs[i][0] - fs[j][0], fs[i][1] - fs[j][1], fs[j][2] - fs[i][2]
                rr = mp.sqrt(A * A + B * B)
                if rr == 0 or abs(C) > rr: continue
                base = mp.atan2(B, A); dl = mp.acos(C / rr)
                for x0 in (base + dl, base - dl):
                    for m in range(-2, 3):
                        x = x0 + 2 * mp.pi * m
                        if a0 < x < a1: cuts.append(x)
        cuts = sorted(cuts)
        for u in range(len(cuts) - 1):
            c0, c1 = cuts[u], cuts[u + 1]
            if c1 - c0 <= 0: continue
            cm = (c0 + c1) / 2
            vals = [f[0] * mp.cos(cm) + f[1] * mp.sin(cm) + f[2] for f in fs]
            fbest = fs[max(range(len(fs)), key=lambda q: vals[q])]
            total += _G(fbest, c1) - _G(fbest, c0); nsub += 1
    return total / 2, nsub


if __name__ == '__main__':
    import sys
    p0 = [-0.01216, 0.0, 0.0, 0.02300, 0.0]
    for K in (1024, 4096, 16384):
        print('poly', K, poly_bounds(p0, K))
    print('exact', exact_area(p0))
    # sanity: single disk and Reuleaux areas
    print('disk area pi/4 =', np.pi / 4, ' B3 area (pi - sqrt3)/2 =', (np.pi - np.sqrt(3)) / 2)
