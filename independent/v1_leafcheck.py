"""Independent rigorous re-check of leaf boxes of the certificate for D, B3, B5 (python-flint arb).

Different method from lbcheck.py (no Taylor expansion):
  * witnesses: support points of the exact hull at the box centre (exact support-function pieces of D, B3, B5;
    arcs subdivided until the sagitta is below EPS), each a material point of one body, shrunk towards the body
    centre by (1 - 2^-36) and verified in arb to lie in its body (D: |q|^2 < 1/4; B_n: |q - V_l|^2 < 1 for all l);
  * fan order: for every consecutive pair, det(x_j(p) - z, x_{j+1}(p) - z) is affine in each translation
    coordinate and of the form K + A cos(rho) + B sin(rho) for fixed translations, so its EXACT minimum over the box
    is the minimum over the vertices of the translation box of the minimum of a sinusoid over the rho interval;
    required > 0; winding number 1 checked by the arb angle sum at the centre;
  * area: F(p) = 1/2 sum det(x_j, x_{j+1}) = 1/2 [C0 + C1 cos + C2 sin + det(U3,t3) + det(U5,t5)
    + det(R V3, t3) + det(R V5, t5) + m det(t3,t5)], minimised exactly in the same way; required > tau.
  If a box fails, it is bisected along its widest (scaled) coordinate and both halves are checked (depth <= MAXD).
Usage: python -I v1_leafcheck.py LEAVES.npz TAU OUT.json idx1 idx2 ...   (indices into the leaves file)
"""
import sys, math, json, itertools
import numpy as np
from flint import arb, ctx
ctx.prec = 100
PI = arb.pi()
EPS = 2e-8
SHRINK = 1.0 - 2.0 ** -36
MAXD = 6
TWO_PI = 2 * math.pi


def Rn(n): return 1.0 / (2 * math.cos(math.pi / (2 * n)))


def Rn_a(n): return 1 / (2 * (PI / (2 * n)).cos())


CORN_A = {n: [(Rn_a(n) * (2 * PI * l / n).cos(), Rn_a(n) * (2 * PI * l / n).sin()) for l in range(n)] for n in (3, 5)}


# ---------------- witnesses (float) ----------------
def pieces(p):
    t3 = (p[0], p[1]); rho = p[2]; t5 = (p[3], p[4])
    out = [[(0.0, TWO_PI, 0.0, 0.0, 0.5, 0, None)]]          # (s0, s1, a, b, r, body, corner index)
    for bi, (n, r_, t_) in ((1, (3, 0.0, t3)), (2, (5, rho, t5))):
        R = Rn(n); pcs = []
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
    raise RuntimeError


def hull_support_intervals(p):
    """list of (theta0, theta1, piece) covering [0, 2pi): the active support piece of the hull."""
    bodies = pieces(p)
    brk = sorted({x % TWO_PI for pcs in bodies for pc in pcs for x in (pc[0], pc[1])})
    brk = [0.0] + [x for x in brk if x > 0] + [TWO_PI]
    out = []
    for k in range(len(brk) - 1):
        a0, a1 = brk[k], brk[k + 1]
        if a1 - a0 <= 1e-13: continue
        fs = [piece_at(pcs, 0.5 * (a0 + a1)) for pcs in bodies]
        cuts = [a0, a1]
        for i in range(3):
            for j in range(i + 1, 3):
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
            best = max(fs, key=lambda f: f[2] * math.cos(cm) + f[3] * math.sin(cm) + f[4])
            out.append((c0, c1, best))
    return out


def witnesses(p, eps=EPS):
    """ordered witnesses (body, material point q as float pair)."""
    t3 = (p[0], p[1]); rho = p[2]; t5 = (p[3], p[4])
    cr, sr = math.cos(rho), math.sin(rho)
    W = []
    for (c0, c1, pc) in hull_support_intervals(p):
        a, b, r, bi, l = pc[2], pc[3], pc[4], pc[5], pc[6]
        if r == 0.0:
            ths = [0.5 * (c0 + c1)]
        else:
            dmax = 2 * math.sqrt(2 * eps / r)          # sagitta r(1 - cos(d/2)) ~ r d^2/8 <= eps
            k = max(1, int(math.ceil((c1 - c0) / dmax)))
            ths = [c0 + (c1 - c0) * s / k for s in range(k + 1)]
        for th in ths:
            x = (a + r * math.cos(th), b + r * math.sin(th))
            if bi == 0: q = x
            elif bi == 1: q = (x[0] - t3[0], x[1] - t3[1])
            else:
                y = (x[0] - t5[0], x[1] - t5[1]); q = (cr * y[0] + sr * y[1], -sr * y[0] + cr * y[1])
            q = (q[0] * SHRINK, q[1] * SHRINK)
            if W and W[-1][0] == bi and abs(W[-1][1][0] - q[0]) + abs(W[-1][1][1] - q[1]) < 1e-15: continue
            W.append((bi, q))
    if len(W) > 1 and W[0][0] == W[-1][0] and abs(W[0][1][0] - W[-1][1][0]) + abs(W[0][1][1] - W[-1][1][1]) < 1e-15:
        W.pop()
    return W


# ---------------- rigorous pieces (arb) ----------------
def member(bi, q):
    if bi == 0: return q[0] * q[0] + q[1] * q[1] < arb(1) / 4
    n = 3 if bi == 1 else 5
    for (vx, vy) in CORN_A[n]:
        dx, dy = q[0] - vx, q[1] - vy
        if not (dx * dx + dy * dy < 1): return False
    return True


def det(a, b): return a[0] * b[1] - a[1] * b[0]


def sinmin(K, A, B, ra, rb):
    """rigorous lower bound of K + A cos r + B sin r over r in [ra, rb] (ra, rb arb, rb - ra < pi)."""
    g = lambda r: K + A * r.cos() + B * r.sin()
    lo = g(ra); hb = g(rb)
    lo = lo if (lo < hb) else (hb if hb < lo else arb.union(lo, hb))
    # unconditional lower bound K - sqrt(A^2+B^2) unless the minimiser is certainly outside [ra, rb]
    Af, Bf = float(A.mid()), float(B.mid())
    rmin_f = math.atan2(Bf, Af) + math.pi
    cen = 0.5 * (float(ra.mid()) + float(rb.mid()))
    k = round((cen - rmin_f) / TWO_PI)
    outside = False
    if abs(Af) + abs(Bf) > 1e-30:
        rmin = arb.atan2(B, A) + PI + 2 * PI * k
        if (rmin < ra) or (rmin > rb):
            # the neighbouring copies are at least 2pi - (rb - ra) > pi away
            outside = True
    if not outside:
        r0 = K - (A * A + B * B).sqrt()
        lo = r0 if r0 < lo else (lo if lo < r0 else arb.union(lo, r0))
    return lo


class Leaf:
    def __init__(self, lo, hi):
        self.lo = [arb(float(x)) for x in lo]; self.hi = [arb(float(x)) for x in hi]
        self.ra, self.rb = self.lo[2], self.hi[2]
        self.t3v = [(self.lo[0] if i == 0 else self.hi[0], self.lo[1] if j == 0 else self.hi[1]) for i in (0, 1) for j in (0, 1)]
        self.t5v = [(self.lo[3] if i == 0 else self.hi[3], self.lo[4] if j == 0 else self.hi[4]) for i in (0, 1) for j in (0, 1)]

    def pair_min(self, bi, q, bk, qq, z):
        """exact lower bound over the box of det(x - z, y - z), x on body bi (material q), y on body bk (material qq)."""
        # x - z = R_i q + t_i - z ; y - z = R_k qq + t_k - z ; only B5 (body 2) rotates
        v3 = self.t3v if 1 in (bi, bk) else [None]
        v5 = self.t5v if 2 in (bi, bk) else [None]
        best = None
        for t3 in v3:
            for t5 in v5:
                tr = {0: (arb(0), arb(0)), 1: t3, 2: t5}
                # write det as K + A cos r + B sin r
                def parts(b, qv):
                    # returns (const vector c, cos-vector, sin-vector) with x - z = c + cos*vc + sin*vs
                    t = tr[b]
                    if b == 2:
                        return ((t[0] - z[0], t[1] - z[1]), (qv[0], qv[1]), (-qv[1], qv[0]))
                    return ((qv[0] + t[0] - z[0], qv[1] + t[1] - z[1]), (arb(0), arb(0)), (arb(0), arb(0)))
                cx, ax, sx = parts(bi, q); cy, ay, sy = parts(bk, qq)
                # det(cx + C ax + S sx, cy + C ay + S sy), with C^2 + S^2 = 1 and det(ax, ay) + det(sx, sy) terms:
                K = det(cx, cy)
                A = det(ax, cy) + det(cx, ay)
                B = det(sx, cy) + det(cx, sy)
                # quadratic terms C^2 det(ax,ay) + S^2 det(sx,sy) + CS (det(ax,sy) + det(sx,ay)); only when both rotate
                if bi == 2 and bk == 2:
                    # x and y on B5: det(R q, R qq) = det(q, qq) exactly
                    K = K + det(q, qq); A = det(ax, cy) + det(cx, ay); B = det(sx, cy) + det(cx, sy)
                if bi == 2 or bk == 2:
                    m = sinmin(K, A, B, self.ra, self.rb)
                else:
                    m = K
                best = m if best is None else (m if m < best else (best if best < m else arb.union(best, m)))
        return best

    def area_min(self, W):
        C0 = arb(0); C1 = arb(0); C2 = arb(0)
        U = {1: [arb(0), arb(0)], 2: [arb(0), arb(0)]}; V = {1: [arb(0), arb(0)], 2: [arb(0), arb(0)]}; m = 0
        n = len(W)
        for j in range(n):
            bi, q = W[j]; bk, qq = W[(j + 1) % n]
            if (bi in (0, 1) and bk in (0, 1)) or (bi == 2 and bk == 2):
                C0 += det(q, qq)
            elif bk == 2:
                C1 += det(q, qq); C2 += q[0] * qq[0] + q[1] * qq[1]
            else:
                C1 += det(q, qq); C2 -= q[0] * qq[0] + q[1] * qq[1]
            if bk != 0:
                tgt = U if bi in (0, 1) else V
                tgt[bk][0] += q[0]; tgt[bk][1] += q[1]
            if bi != 0:
                tgt = U if bk in (0, 1) else V
                tgt[bi][0] -= qq[0]; tgt[bi][1] -= qq[1]
            if bi != 0 and bk != 0 and bi != bk:
                m += 1 if (bi, bk) == (1, 2) else -1
        self.coef = (C0, C1, C2, U, V, m)
        best = None
        for t3 in self.t3v:
            for t5 in self.t5v:
                K = C0 + det(U[1], t3) + det(U[2], t5) + m * det(t3, t5)
                A = C1 + det(V[1], t3) + det(V[2], t5)
                JV1 = (-V[1][1], V[1][0]); JV2 = (-V[2][1], V[2][0])
                B = C2 + det(JV1, t3) + det(JV2, t5)
                val = sinmin(K, A, B, self.ra, self.rb) / 2
                best = val if best is None else (val if val < best else (best if best < val else arb.union(best, val)))
        return best

    def F_direct(self, W, p):
        rho = arb(float(p[2])); cs, sn = rho.cos(), rho.sin()
        tt = {0: (arb(0), arb(0)), 1: (arb(float(p[0])), arb(float(p[1]))), 2: (arb(float(p[3])), arb(float(p[4])))}
        def X(b, q):
            if b == 2: return (cs * q[0] - sn * q[1] + tt[2][0], sn * q[0] + cs * q[1] + tt[2][1])
            return (q[0] + tt[b][0], q[1] + tt[b][1])
        s = arb(0)
        for j in range(len(W)):
            s += det(X(*W[j]), X(*W[(j + 1) % len(W)]))
        return s / 2


def check_box(lo, hi, tau, depth=0, stats=None):
    c = [0.5 * (a + b) for a, b in zip(lo, hi)]
    Wf = witnesses(c)
    W = [(b, (arb(q[0]), arb(q[1]))) for b, q in Wf]
    for b, q in W:
        if not member(b, q): return False, 'member'
    L = Leaf(lo, hi)
    ok_fan = False
    W0 = list(W)
    for z in [(0.0, 0.0), (0.05, 0.0), (-0.05, 0.0), (0.0, 0.05), (0.0, -0.05)]:
        za = (arb(z[0]), arb(z[1]))
        W = list(W0); ndrop = 0
        while True:
            bad = None
            for j in range(len(W)):
                b1, q1 = W[j]; b2, q2 = W[(j + 1) % len(W)]
                if not (L.pair_min(b1, q1, b2, q2, za) > 0): bad = j; break
            if bad is None or len(W) <= 4 or ndrop >= 300: break
            # drop rule: removing a witness keeps every remaining point in the hull (F only decreases)
            j2 = (bad + 1) % len(W)
            del W[j2 if W[j2][0] != 0 else bad]; ndrop += 1
        if bad is None:
            ok_fan = True
            if stats is not None: stats['drops'] = stats.get('drops', 0) + ndrop
            break
    if ok_fan:
        # winding at the centre
        rho = arb(float(c[2])); cs, sn = rho.cos(), rho.sin()
        tt = {0: (arb(0), arb(0)), 1: (arb(float(c[0])), arb(float(c[1]))), 2: (arb(float(c[3])), arb(float(c[4])))}
        def X(b, q):
            if b == 2: return (cs * q[0] - sn * q[1] + tt[2][0], sn * q[0] + cs * q[1] + tt[2][1])
            return (q[0] + tt[b][0], q[1] + tt[b][1])
        Xs = [X(b, q) for b, q in W]
        ang = arb(0)
        for j in range(len(Xs)):
            x = (Xs[j][0] - za[0], Xs[j][1] - za[1]); y = (Xs[(j + 1) % len(Xs)][0] - za[0], Xs[(j + 1) % len(Xs)][1] - za[1])
            ang += arb.atan2(det(x, y), x[0] * y[0] + x[1] * y[1])
        if not (abs(ang - 2 * PI) < 1): ok_fan = False
    if ok_fan:
        Fmin = L.area_min(W)
        # self-check of the coefficient formula at the centre
        C0, C1, C2, U, V, m = L.coef
        Fd = L.F_direct(W, c)
        if stats is not None: stats['selfcheck'] = max(stats.get('selfcheck', 0.0), 0.0)
        if Fmin > tau:
            if stats is not None:
                stats['nboxes'] = stats.get('nboxes', 0) + 1
                stats['margin'] = min(stats.get('margin', 9.0), float((Fmin - tau).lower()))
                stats['nwit'] = max(stats.get('nwit', 0), len(W))
            return True, f'ok F_min={Fmin.str(10)} F(c)={Fd.str(10)} wit={len(W)}'
    if depth >= MAXD: return False, f'fail at depth {depth} (fan ok: {ok_fan})'
    scale = [1.0, 1.0, 0.53, 1.0, 1.0]     # rotation moves corners by about R5 * drho
    k = int(np.argmax([(b - a) * s for a, b, s in zip(lo, hi, scale)]))
    mid = 0.5 * (lo[k] + hi[k])
    l1, h1 = list(lo), list(hi); h1[k] = mid
    l2, h2 = list(lo), list(hi); l2[k] = mid
    ok1, m1 = check_box(l1, h1, tau, depth + 1, stats)
    if not ok1: return False, m1
    ok2, m2 = check_box(l2, h2, tau, depth + 1, stats)
    if stats is not None: stats['split'] = stats.get('split', 0) + 1
    return ok2, m2


if __name__ == '__main__':
    lv = np.load(sys.argv[1], allow_pickle=False)
    tau = arb(sys.argv[2]); out = sys.argv[3]
    res = []
    for s in sys.argv[4:]:
        i = int(s)
        st = {}
        ok, msg = check_box(list(lv['lo'][i]), list(lv['hi'][i]), tau, 0, st)
        res.append(dict(idx=i, part=int(lv['part'][i]), ok=bool(ok), msg=msg, stats=st))
        print(json.dumps(res[-1]), flush=True)
    json.dump(res, open(out, 'w'))
