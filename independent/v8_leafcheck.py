"""Independent rigorous re-check of leaf boxes of the certificate for D, B3, B5, B7 (python-flint arb).

Same method as v1_leafcheck.py, generalised to two rotating bodies:
  * witnesses: support points of the exact hull at the box centre (gen8.witnesses), shrunk by 1 - 2^-36, membership
    verified in arb;
  * for fixed rotations every fan determinant and the fan area F are affine in each of the six translation
    coordinates, so box minima over translations are attained at vertices (<= 64);
  * for fixed translations they are K + A5 cos r5 + B5 sin r5 + A7 cos r7 + B7 sin r7 + C cos(r7-r5) + S sin(r7-r5):
    minimised over the rotation box by exact minima on its edges, interior critical points being excluded when a
    partial derivative has constant sign (2 x 2 splits up to depth 4), and otherwise with arb sub-intervals in r5
    (MSUB pieces) and an exact sinusoid minimum in r7;
  * drop rule for fan-order failures; winding 1 at the centre; bisection of failing boxes (depth <= MAXD).
Usage: python -I v8_leafcheck.py LEAVES.npz TAU OUT.json idx ...
"""
import sys, os, math, json
import numpy as np
from flint import arb, ctx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen8
ctx.prec = 100
PI = arb.pi(); TWO_PI = 2 * math.pi
MAXD = 5; MSUB = 16
ROT = {2: 2, 3: 5}            # body -> index of its rotation parameter
TR = {1: (0, 1), 2: (3, 4), 3: (6, 7)}
CORN = {n: [((1 / (2 * (PI / (2 * n)).cos())) * (2 * PI * l / n).cos(), (1 / (2 * (PI / (2 * n)).cos())) * (2 * PI * l / n).sin())
            for l in range(n)] for n in (3, 5, 7)}
NOF = {1: 3, 2: 5, 3: 7}


def det(a, b): return a[0] * b[1] - a[1] * b[0]
def J(v): return (-v[1], v[0])
def amin(a, b): return a if a < b else (b if b < a else arb.union(a, b))


def member(bi, q):
    if bi == 0: return q[0] * q[0] + q[1] * q[1] < arb(1) / 4
    for (vx, vy) in CORN[NOF[bi]]:
        dx, dy = q[0] - vx, q[1] - vy
        if not (dx * dx + dy * dy < 1): return False
    return True


def sinmin(K, A, B, ra, rb):
    g = lambda r: K + A * r.cos() + B * r.sin()
    lo = amin(g(ra), g(rb))
    Af, Bf = float(A.mid()), float(B.mid())
    outside = False
    if abs(Af) + abs(Bf) > 1e-30:
        rmin_f = math.atan2(Bf, Af) + math.pi
        cen = 0.5 * (float(ra.mid()) + float(rb.mid()))
        k = round((cen - rmin_f) / TWO_PI)
        rmin = arb.atan2(B, A) + PI + 2 * PI * k
        if (rmin < ra) or (rmin > rb): outside = True
    if not outside:
        lo = amin(lo, K - (A * A + B * B).sqrt())
    return lo


class Box:
    def __init__(self, lo, hi):
        self.lo = [arb(float(x)) for x in lo]; self.hi = [arb(float(x)) for x in hi]
        self.I = {2: (self.lo[2], self.hi[2]), 3: (self.lo[5], self.hi[5])}
        self.V = {}
        for b, (ix, iy) in TR.items():
            self.V[b] = [(self.lo[ix] if i == 0 else self.hi[ix], self.lo[iy] if j == 0 else self.hi[iy]) for i in (0, 1) for j in (0, 1)]
        # rotation sub-intervals for r5 (arb balls covering [lo, hi])
        a, b = self.lo[2], self.hi[2]
        self.sub5 = [arb.union(a + (b - a) * s / MSUB, a + (b - a) * (s + 1) / MSUB) for s in range(MSUB)]

    def trigmin(self, K, A, B, C, S):
        """lower bound of K + sum_r (A_r cos r + B_r sin r) + C cos(r7-r5) + S sin(r7-r5) over the rotation box.
        A, B: dicts body -> arb (missing = 0)."""
        has5 = 2 in A; has7 = 3 in A
        cross = (C is not None)
        if not cross:
            v = K
            if has5: v = v + sinmin(arb(0), A[2], B[2], *self.I[2])
            if has7: v = v + sinmin(arb(0), A[3], B[3], *self.I[3])
            return v
        A5 = A.get(2, arb(0)); B5 = B.get(2, arb(0)); A7 = A.get(3, arb(0)); B7 = B.get(3, arb(0))
        v = self.cross_min(K, A5, B5, A7, B7, C, S, self.I[2], self.I[3], 0)
        if v is not None: return v
        best = None
        for r5 in self.sub5:
            c5, s5 = r5.cos(), r5.sin()
            Kp = K + A5 * c5 + B5 * s5
            Ap = A7 + C * c5 - S * s5
            Bp = B7 + C * s5 + S * c5
            v = sinmin(Kp, Ap, Bp, *self.I[3])
            best = v if best is None else amin(best, v)
        return best

    def cross_min(self, K, A5, B5, A7, B7, C, S, I5, I7, depth):
        """exact-edge minimum of g = K + A5 c5 + B5 s5 + A7 c7 + B7 s7 + C cos(r7-r5) + S sin(r7-r5) over I5 x I7:
        the four edges are sinusoids (exact sinmin); interior critical points are excluded when a partial derivative
        has constant sign on the box (interval evaluation), otherwise the box is split in 2 x 2 (depth <= 4);
        returns None if not resolved."""
        (a5, b5), (a7, b7) = I5, I7
        def edge7(r7):   # g as a sinusoid in r5 for fixed r7
            c7, s7 = r7.cos(), r7.sin()
            return sinmin(K + A7 * c7 + B7 * s7, A5 + C * c7 + S * s7, B5 + C * s7 - S * c7, a5, b5)
        def edge5(r5):   # g as a sinusoid in r7 for fixed r5
            c5, s5 = r5.cos(), r5.sin()
            return sinmin(K + A5 * c5 + B5 * s5, A7 + C * c5 - S * s5, B7 + C * s5 + S * c5, a7, b7)
        e = amin(amin(edge7(a7), edge7(b7)), amin(edge5(a5), edge5(b5)))
        R5, R7 = arb.union(a5, b5), arb.union(a7, b7)
        d = R7 - R5
        g5 = -A5 * R5.sin() + B5 * R5.cos() + C * d.sin() - S * d.cos()
        g7 = -A7 * R7.sin() + B7 * R7.cos() - C * d.sin() + S * d.cos()
        if (g5 > 0) or (g5 < 0) or (g7 > 0) or (g7 < 0):
            return e
        if depth >= 4: return None
        m5, m7 = (a5 + b5) / 2, (a7 + b7) / 2
        best = e
        for J5 in ((a5, m5), (m5, b5)):
            for J7 in ((a7, m7), (m7, b7)):
                v = self.cross_min(K, A5, B5, A7, B7, C, S, J5, J7, depth + 1)
                if v is None: return None
                best = amin(best, v)
        return best

    def pair_min(self, bi, q, bk, qq, z):
        bodies_t = [b for b in (bi, bk) if b != 0]
        tb = sorted(set(bodies_t))
        best = None
        import itertools
        for combo in itertools.product(*[self.V[b] for b in tb]):
            tv = dict(zip(tb, combo))
            a = {b: ((tv[b][0] - z[0]), (tv[b][1] - z[1])) if b != 0 else (-z[0], -z[1]) for b in (bi, bk)}
            K = arb(0); A = {}; B = {}; C = None; S = None
            def addA(b, va, vb):
                A[b] = A.get(b, arb(0)) + va; B[b] = B.get(b, arb(0)) + vb
            ri, rk = bi in ROT, bk in ROT
            # term 1
            if (not ri and not rk) or bi == bk: K += det(q, qq)
            elif not ri and rk: addA(bk, det(q, qq), q[0] * qq[0] + q[1] * qq[1])
            elif ri and not rk: addA(bi, det(q, qq), -(q[0] * qq[0] + q[1] * qq[1]))
            else:
                sg = 1 if (bi, bk) == (2, 3) else -1
                C = det(q, qq); S = sg * (q[0] * qq[0] + q[1] * qq[1])
            # term 2: det(R_i q, a_k)
            if not ri: K += det(q, a[bk])
            else: addA(bi, det(q, a[bk]), det(J(q), a[bk]))
            # term 3: det(a_i, R_k qq)
            if not rk: K += det(a[bi], qq)
            else: addA(bk, det(a[bi], qq), det(a[bi], J(qq)))
            # term 4
            K += det(a[bi], a[bk])
            v = self.trigmin(K, A, B, C, S)
            best = v if best is None else amin(best, v)
        return best

    def area_min(self, W):
        # accumulate F = 1/2 [C0 + sum det(U_b,t_b) + sum m_bc det(t_b,t_c) + sum_r cos r (A0_r + sum det(V_rb,t_b))
        #                    + sin r (B0_r + sum det(J V_rb, t_b)) + C cos(r7-r5) + S sin(r7-r5)]
        z2 = (arb(0), arb(0))
        C0 = arb(0); A0 = {2: arb(0), 3: arb(0)}; B0 = {2: arb(0), 3: arb(0)}; Cc = arb(0); Sc = arb(0)
        U = {b: [arb(0), arb(0)] for b in (1, 2, 3)}
        Vr = {(r, b): [arb(0), arb(0)] for r in (2, 3) for b in (1, 2, 3)}
        m = {(1, 2): 0, (1, 3): 0, (2, 3): 0}
        n = len(W)
        for j in range(n):
            bi, q = W[j]; bk, qq = W[(j + 1) % n]
            ri, rk = bi in ROT, bk in ROT
            dq = det(q, qq); dd = q[0] * qq[0] + q[1] * qq[1]
            if (not ri and not rk) or bi == bk: C0 += dq
            elif not ri and rk: A0[bk] += dq; B0[bk] += dd
            elif ri and not rk: A0[bi] += dq; B0[bi] -= dd
            else:
                Cc += dq; Sc += dd if (bi, bk) == (2, 3) else -dd
            if bk != 0:
                tgt = U[bk] if not ri else Vr[(bi, bk)]
                tgt[0] += q[0]; tgt[1] += q[1]
            if bi != 0:
                tgt = U[bi] if not rk else Vr[(bk, bi)]
                tgt[0] -= qq[0]; tgt[1] -= qq[1]
            if bi != 0 and bk != 0 and bi != bk:
                if bi < bk: m[(bi, bk)] += 1
                else: m[(bk, bi)] -= 1
        self.coef = (C0, A0, B0, Cc, Sc, U, Vr, m)
        best = None
        import itertools
        for t1, t2, t3 in itertools.product(self.V[1], self.V[2], self.V[3]):
            T = {1: t1, 2: t2, 3: t3}
            K = C0 + sum((det(U[b], T[b]) for b in (1, 2, 3)), arb(0))
            K += m[(1, 2)] * det(t1, t2) + m[(1, 3)] * det(t1, t3) + m[(2, 3)] * det(t2, t3)
            A = {}; B = {}
            for r in (2, 3):
                A[r] = A0[r] + sum((det(Vr[(r, b)], T[b]) for b in (1, 2, 3)), arb(0))
                B[r] = B0[r] + sum((det(J(Vr[(r, b)]), T[b]) for b in (1, 2, 3)), arb(0))
            v = self.trigmin(K, A, B, Cc, Sc) / 2
            best = v if best is None else amin(best, v)
        return best


def X_at(p, b, q):
    if b == 0: return q
    if b == 1: return (q[0] + p[0], q[1] + p[1])
    r = arb(float(p[ROT[b]])); cs, sn = r.cos(), r.sin(); ix, iy = TR[b]
    return (cs * q[0] - sn * q[1] + arb(float(p[ix])), sn * q[0] + cs * q[1] + arb(float(p[iy])))


def check_box(lo, hi, tau, depth=0, stats=None):
    c = [0.5 * (a + b) for a, b in zip(lo, hi)]
    W0 = [(b, (arb(q[0]), arb(q[1]))) for b, q in gen8.witnesses(c)]
    for b, q in W0:
        if not member(b, q): return False, 'member'
    bx = Box(lo, hi)
    ok_fan = False
    for zf in [(0.0, 0.0), (0.05, 0.0), (-0.05, 0.0), (0.0, 0.05), (0.0, -0.05)]:
        z = (arb(zf[0]), arb(zf[1])); W = list(W0); nd = 0
        while True:
            bad = None
            for j in range(len(W)):
                b1, q1 = W[j]; b2, q2 = W[(j + 1) % len(W)]
                if not (bx.pair_min(b1, q1, b2, q2, z) > 0): bad = j; break
            if bad is None or len(W) <= 4 or nd >= 300: break
            j2 = (bad + 1) % len(W); del W[j2 if W[j2][0] != 0 else bad]; nd += 1
        if bad is None:
            Xs = [X_at(c, b, q) for b, q in W]
            ang = arb(0)
            for j in range(len(Xs)):
                x = (Xs[j][0] - z[0], Xs[j][1] - z[1]); y = (Xs[(j + 1) % len(Xs)][0] - z[0], Xs[(j + 1) % len(Xs)][1] - z[1])
                ang += arb.atan2(det(x, y), x[0] * y[0] + x[1] * y[1])
            if abs(ang - 2 * PI) < 1:
                ok_fan = True
                if stats is not None: stats['drops'] = stats.get('drops', 0) + nd
                break
    if ok_fan:
        Fmin = bx.area_min(W)
        if Fmin > tau:
            if stats is not None:
                stats['nboxes'] = stats.get('nboxes', 0) + 1
                stats['margin'] = min(stats.get('margin', 9.0), float((Fmin - tau).lower()))
                stats['nwit'] = max(stats.get('nwit', 0), len(W))
            return True, f'ok F_min={Fmin.str(10)} wit={len(W)}'
    if depth >= MAXD: return False, f'fail at depth {depth} (fan ok: {ok_fan})'
    scale = [1, 1, 0.53, 1, 1, 0.51, 1, 1]
    k = int(np.argmax([(b - a) * s for a, b, s in zip(lo, hi, scale)]))
    mid = 0.5 * (lo[k] + hi[k])
    l1, h1 = list(lo), list(hi); h1[k] = mid; l2, h2 = list(lo), list(hi); l2[k] = mid
    ok1, m1 = check_box(l1, h1, tau, depth + 1, stats)
    if not ok1: return False, m1
    if stats is not None: stats['split'] = stats.get('split', 0) + 1
    return check_box(l2, h2, tau, depth + 1, stats)


if __name__ == '__main__':
    lv = np.load(sys.argv[1], allow_pickle=False); tau = arb(sys.argv[2]); res = []
    for s in sys.argv[4:]:
        i = int(s); st = {}
        ok, msg = check_box(list(lv['lo'][i]), list(lv['hi'][i]), tau, 0, st)
        res.append(dict(idx=i, part=int(lv['part'][i]), ok=bool(ok), msg=msg, stats=st)); print(json.dumps(res[-1]), flush=True)
    json.dump(res, open(sys.argv[3], 'w'))
