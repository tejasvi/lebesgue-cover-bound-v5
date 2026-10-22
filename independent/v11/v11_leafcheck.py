"""V11 (audit): independent rigorous re-check of 11D leaf boxes (D, B3, B5, B7, B9), python-flint arb.

Same method as audit8/v8_leafcheck.py (written for the 8D audit), generalised to three rotating bodies:
  * witnesses: support points of the exact hull (gen11.witnesses: exact support-function pieces, arcs subdivided to
    sagitta <= eps), shrunk by 1 - 2^-44; membership in the body verified in arb;
  * fan order: each consecutive determinant det(X_j - z, X_{j+1} - z), X = R(r_b) q + t_b, is minimised over the whole
    box: it is affine in each translation coordinate (minimum at a vertex of the translation box) and a trigonometric
    polynomial in the rotations, minimised exactly (tmin below); drop rule on failure; winding 1 at the box centre;
  * area: one fan F (code 254 leaves), or sum_i mu_i F_i (code 253 leaves: the certificate's shift points c + s_i h
    give the witness positions and its weights lam_i give mu_i = lam_i / sum lam, normalised in arb; every F_i is a fan
    verified on the whole box, so A >= F_i on the box and A >= sum mu_i F_i). The bound is multi-affine in the eight
    translation coordinates, so its box minimum is attained at one of the 256 vertices; at each vertex it is
    K + sum_b (A_b cos r_b + B_b sin r_b) + sum_{b<c} (C_bc cos(r_c - r_b) + S_bc sin(r_c - r_b)) in the rotations;
  * tmin: exact minimum of that trigonometric polynomial over the rotation box: a variable whose partial derivative
    has constant sign on the box (interval evaluation) is fixed at the lower or upper end of its interval; with one
    free variable left the minimum of K + A cos r + B sin r over an interval shorter than pi is taken at an end point or
    is K - sqrt(A^2 + B^2) (the derivative signs at both ends and the sign of f'' on the interval decide); otherwise
    the box is bisected (depth <= TDMAX),
    and at the bottom all but one variable are replaced by their interval enclosures (a valid lower bound);
  * a failing leaf box is bisected (depth <= MAXD); each piece is checked with its own centre fan, and for code 253
    also with the parent's structures (same witness lists and weights, fans re-verified on the piece).
Verdict per leaf: the minimum over the box of the lower bound exceeds tau (an arb ball of the header's decimal string).
Usage: python -I v11_leafcheck.py LEAVES.npz OUT.jsonl [idx ...]  (LEAVES.npz from v11_sample.py)
"""
import sys, os, math, json, time
sys.dont_write_bytecode = True
import numpy as np
from flint import arb, ctx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen11
ctx.prec = 128
PI = arb.pi()
ROT = {2: 2, 3: 5, 4: 8}                        # body -> index of its rotation parameter
TR = {1: (0, 1), 2: (3, 4), 3: (6, 7), 4: (9, 10)}
NOF = {1: 3, 2: 5, 3: 7, 4: 9}
RB = (2, 3, 4)
PAIRS = ((2, 3), (2, 4), (3, 4))
CORN = {n: [((1 / (2 * (PI / (2 * n)).cos())) * (2 * PI * l / n).cos(), (1 / (2 * (PI / (2 * n)).cos())) * (2 * PI * l / n).sin())
            for l in range(n)] for n in (3, 5, 7, 9)}
TDMAX = 36
MAXDROP = 4000
TSTAT = {'fallback': 0}
MAXD = 4
ZC = [(0.0, 0.0), (0.05, 0.0), (-0.05, 0.0), (0.0, 0.05), (0.0, -0.05), (0.1, 0.1), (-0.1, 0.1), (0.1, -0.1), (-0.1, -0.1)]
ZERO = arb(0)


def det(a, b): return a[0] * b[1] - a[1] * b[0]
def J(v): return (-v[1], v[0])
def amin(a, b): return a if a < b else (b if b < a else arb.union(a, b))


def member(bi, q):
    if bi == 0: return q[0] * q[0] + q[1] * q[1] < arb(1) / 4
    for (vx, vy) in CORN[NOF[bi]]:
        dx, dy = q[0] - vx, q[1] - vy
        if not (dx * dx + dy * dy < 1): return False
    return True


class Trig:
    """cos/sin of exact float end points and of interval balls (cached per box)."""
    def __init__(self):
        self.pt = {}; self.iv = {}; self.df = {}
    def _trim(self):
        if len(self.pt) + len(self.iv) + len(self.df) > 60000: self.pt.clear(); self.iv.clear(); self.df.clear()
    def point(self, x):
        self._trim()
        v = self.pt.get(x)
        if v is None:
            a = arb(x); v = (a.cos(), a.sin()); self.pt[x] = v
        return v
    def ball(self, iv):
        v = self.iv.get(iv)
        if v is None:
            u = arb.union(arb(iv[0]), arb(iv[1])); v = (u, u.cos(), u.sin()); self.iv[iv] = v
        return v
    def diff(self, ivc, ivb):      # cos/sin of the ball r_c - r_b
        key = (ivc, ivb); v = self.df.get(key)
        if v is None:
            d = self.ball(ivc)[0] - self.ball(ivb)[0]; v = (d.cos(), d.sin()); self.df[key] = v
        return v


def sin1(K, A, B, iv, cs):
    """exact lower bound of K + A cos r + B sin r over r in iv = (a, b), b - a < pi; cs = Trig."""
    ca, sa = cs.point(iv[0]); cb, sb = cs.point(iv[1])
    lo = amin(K + A * ca + B * sa, K + A * cb + B * sb)
    da = -A * sa + B * ca; db = -A * sb + B * cb
    if (da > 0) or (db < 0): return lo
    _, ci, si = cs.ball(iv)
    if A * ci + B * si > 0: return lo           # f'' = -(A cos r + B sin r) < 0 on the interval: concave, minimum at an end
    return amin(lo, K - (A * A + B * B).sqrt())


def fix(f, b, c, s):
    """substitute cos r_b = c, sin r_b = s (points or balls) into f = (K, A, B, C, S)."""
    K, A, B, C, S = f
    K = K + A.get(b, ZERO) * c + B.get(b, ZERO) * s
    A = {k: v for k, v in A.items() if k != b}; B = {k: v for k, v in B.items() if k != b}
    C2, S2 = {}, {}
    for (x, y), Cv in C.items():
        Sv = S[(x, y)]
        if x == b:      # C cos(r_y - v) + S sin(r_y - v)
            A[y] = A.get(y, ZERO) + Cv * c - Sv * s; B[y] = B.get(y, ZERO) + Cv * s + Sv * c
        elif y == b:    # C cos(v - r_x) + S sin(v - r_x)
            A[x] = A.get(x, ZERO) + Cv * c + Sv * s; B[x] = B.get(x, ZERO) + Cv * s - Sv * c
        else:
            C2[(x, y)] = Cv; S2[(x, y)] = Sv
    return (K, A, B, C2, S2)


def _depends(f, b):
    K, A, B, C, S = f
    if b in A and not (A[b].is_zero() and B[b].is_zero()): return True
    return any(b in pr and not (C[pr].is_zero() and S[pr].is_zero()) for pr in C)


def _reduce(f, I):
    """drop the variables on which f does not depend (all their coefficients exactly 0)."""
    K, A, B, C, S = f
    free = [b for b in I if _depends(f, b)]
    if len(free) < len(I):
        I = {b: I[b] for b in free}
        A = {b: v for b, v in A.items() if b in I}; B = {b: v for b, v in B.items() if b in I}
        C = {pr: v for pr, v in C.items() if pr[0] in I and pr[1] in I}; S = {pr: S[pr] for pr in C}
        f = (K, A, B, C, S)
    return f, I


def _derivs(f, I, cs):
    """interval enclosures of the partial derivatives of f over the box I."""
    K, A, B, C, S = f; out = {}
    for b in I:
        Rb, cb, sb = cs.ball(I[b])
        d = -A.get(b, ZERO) * sb + B.get(b, ZERO) * cb
        for (x, y), Cv in C.items():
            Sv = S[(x, y)]
            if x == b:
                cd, sd = cs.diff(I[y], I[b]); d += Cv * sd - Sv * cd
            elif y == b:
                cd, sd = cs.diff(I[b], I[x]); d += -Cv * sd + Sv * cd
        out[b] = d
    return out


def _fpoint(f, pt, cs):
    """f at the point pt = {b: float}."""
    K, A, B, C, S = f; v = K; tr = {b: cs.point(x) for b, x in pt.items()}
    for b, (c, s) in tr.items(): v += A.get(b, ZERO) * c + B.get(b, ZERO) * s
    for (x, y), Cv in C.items():
        cx, sx = tr[x]; cy, sy = tr[y]
        v += Cv * (cy * cx + sy * sx) + S[(x, y)] * (sy * cx - cy * sx)
    return v


def tmin(f, I, cs, depth=0, budget=None, target=None):
    """lower bound (exact up to arb rounding when the budget suffices) of f over the rotation box I = {b: (lo, hi)}:
    variables without dependence are dropped; one free variable: exact sinusoid minimum; a variable whose partial
    derivative has constant sign on the box is fixed at the lower/upper end; otherwise best-first branch and bound.
    target (optional): the branch and bound stops once the bound is within 1% of (minimum - target), or at once if a
    point value is below target; the result is a valid lower bound in every case."""
    if budget is None: budget = [20000]
    budget[0] -= 1
    f, I = _reduce(f, I)
    K, A, B, C, S = f
    if not I: return K
    if len(I) == 1:
        (b,) = I
        return sin1(K, A.get(b, ZERO), B.get(b, ZERO), I[b], cs)
    d = _derivs(f, I, cs)
    for b in I:
        if d[b] > 0 or d[b] < 0:
            c, s = cs.point(I[b][0] if d[b] > 0 else I[b][1])
            return tmin(fix(f, b, c, s), {k: v for k, v in I.items() if k != b}, cs, depth, budget, target)
    return _bnb(f, I, cs, budget, d, target)


def _node_lb(f, Q, cs, budget, d=None, target=None):
    """valid lower bound of f over the box Q: exact face reduction if a derivative has constant sign, else the
    mean-value form f(c) - sum_b |df/dr_b (Q)| h_b with h_b the larger distance from c_b to the ends of Q_b."""
    if d is None: d = _derivs(f, Q, cs)
    for b in Q:
        if d[b] > 0 or d[b] < 0:
            c, s = cs.point(Q[b][0] if d[b] > 0 else Q[b][1])
            return tmin(fix(f, b, c, s), {k: v for k, v in Q.items() if k != b}, cs, 0, budget, target), True
    ctr = {b: 0.5 * (Q[b][0] + Q[b][1]) for b in Q}
    v = _fpoint(f, ctr, cs)
    for b in Q:
        hb = max(arb(ctr[b]) - arb(Q[b][0]), arb(Q[b][1]) - arb(ctr[b]))
        v -= abs(d[b]) * hb
    return v, False


def _bnb(f, I, cs, budget, d0, target=None):
    import heapq
    TSTAT['bnb'] = TSTAT.get('bnb', 0) + 1
    lb0, _ = _node_lb(f, I, cs, budget, d0, target)
    ub = float(_fpoint(f, {b: 0.5 * (I[b][0] + I[b][1]) for b in I}, cs).mid())
    heap = [(float(lb0.lower()), 0, I, lb0)]; cnt = 1
    while heap:
        lbf, _, Q, lba = heap[0]
        if target is not None and ub < target: break
        tol = 1e-13 if target is None else max(1e-13, 0.01 * (ub - target))
        if lbf >= ub - tol or budget[0] <= 0: break
        heapq.heappop(heap)
        b = max(Q, key=lambda k: Q[k][1] - Q[k][0]); a0, a1 = Q[b]; m = 0.5 * (a0 + a1)
        if not (a0 < m < a1):                        # cannot split further: keep the node's bound
            heapq.heappush(heap, (lbf, cnt, Q, lba)); cnt += 1; break
        for half in ((a0, m), (m, a1)):
            Q2 = dict(Q); Q2[b] = half; budget[0] -= 1
            lb2, _ = _node_lb(f, Q2, cs, budget, None, target)
            ub = min(ub, float(_fpoint(f, {k: 0.5 * (Q2[k][0] + Q2[k][1]) for k in Q2}, cs).mid()))
            heapq.heappush(heap, (float(lb2.lower()), cnt, Q2, lb2)); cnt += 1
    if budget[0] <= 0: TSTAT['budget'] = TSTAT.get('budget', 0) + 1
    res = None
    for _, _, _, lba in heap: res = lba if res is None else amin(res, lba)
    return res


class Box:
    def __init__(self, lo, hi):
        self.lof = [float(x) for x in lo]; self.hif = [float(x) for x in hi]
        self.c = [0.5 * (a + b) for a, b in zip(self.lof, self.hif)]
        self.I = {b: (self.lof[ROT[b]], self.hif[ROT[b]]) for b in RB}
        for b in RB: assert self.I[b][1] - self.I[b][0] < 3.0
        self.V = {b: [(arb(self.lof[ix] if i == 0 else self.hif[ix]), arb(self.lof[iy] if j == 0 else self.hif[iy]))
                      for i in (0, 1) for j in (0, 1)] for b, (ix, iy) in TR.items()}
        self.cs = Trig()

    def pair_min(self, bi, q, bk, qq, z):
        """lower bound over the box of det(X_i - z, X_k - z)."""
        cs = self.cs
        if bi == bk:
            if bi == 0:
                return det((q[0] - z[0], q[1] - z[1]), (qq[0] - z[0], qq[1] - z[1]))
            w = (q[0] - qq[0], q[1] - qq[1]); K0 = det(q, qq); best = None
            for tv in self.V[bi]:
                a = (tv[0] - z[0], tv[1] - z[1])
                if bi in ROT: v = sin1(K0, det(w, a), det(J(w), a), self.I[bi], cs)
                else: v = K0 + det(w, a)
                best = v if best is None else amin(best, v)
            return best
        best = None
        Vi = self.V[bi] if bi != 0 else [None]; Vk = self.V[bk] if bk != 0 else [None]
        ri, rk = bi in ROT, bk in ROT
        dq = det(q, qq); dd = q[0] * qq[0] + q[1] * qq[1]
        for ti in Vi:
            ai = (-z[0], -z[1]) if ti is None else (ti[0] - z[0], ti[1] - z[1])
            for tk in Vk:
                ak = (-z[0], -z[1]) if tk is None else (tk[0] - z[0], tk[1] - z[1])
                K = det(ai, ak); A = {}; B = {}; C = {}; S = {}
                if not ri and not rk: K += dq
                elif not ri and rk: A[bk] = dq; B[bk] = dd
                elif ri and not rk: A[bi] = dq; B[bi] = -dd
                elif bi < bk: C[(bi, bk)] = dq; S[(bi, bk)] = dd
                else: C[(bk, bi)] = dq; S[(bk, bi)] = -dd
                if ri: A[bi] = A.get(bi, ZERO) + det(q, ak); B[bi] = B.get(bi, ZERO) + det(J(q), ak)
                else: K += det(q, ak)
                if rk: A[bk] = A.get(bk, ZERO) + det(ai, qq); B[bk] = B.get(bk, ZERO) + det(ai, J(qq))
                else: K += det(ai, qq)
                I = {b: self.I[b] for b in (bi, bk) if b in ROT}
                v = tmin((K, A, B, C, S), I, cs, target=0.0)
                best = v if best is None else amin(best, v)
        return best

    def X_center(self, b, q):
        p = self.c
        if b == 0: return q
        ix, iy = TR[b]
        if b not in ROT: return (q[0] + arb(p[ix]), q[1] + arb(p[iy]))
        r = arb(p[ROT[b]]); c, s = r.cos(), r.sin()
        return (c * q[0] - s * q[1] + arb(p[ix]), s * q[0] + c * q[1] + arb(p[iy]))

    def make_fan(self, W0, z, stats, rule=0):
        """drop rule until every consecutive pair has a positive determinant on the box; then winding 1 at the centre.
        rule 0 drops the later witness of a failing pair (the earlier one if the later is on the disk), rule 1 the
        earlier one (the later one if the earlier is on the disk)."""
        from collections import deque
        n0 = len(W0); nxt = [(i + 1) % n0 for i in range(n0)]; prv = [(i - 1) % n0 for i in range(n0)]
        alive = [True] * n0; queued = [True] * n0; todo = deque(range(n0)); count = n0; nd = 0
        while todo:                                 # each live pair (i, nxt[i]) is checked in its final form
            i = todo.popleft(); queued[i] = False
            if not alive[i]: continue
            k = nxt[i]
            if self.pair_min(W0[i][0], W0[i][1], W0[k][0], W0[k][1], z) > 0: continue
            if count <= 4 or nd >= MAXDROP: return None, 'too many drops'
            if rule == 0: d = k if W0[k][0] != 0 else i
            else: d = i if W0[i][0] != 0 else k
            alive[d] = False; pd, qd = prv[d], nxt[d]; nxt[pd] = qd; prv[qd] = pd; count -= 1; nd += 1
            if not queued[pd]: todo.appendleft(pd); queued[pd] = True    # the new pair (pd, qd)
        st = next(i for i in range(n0) if alive[i]); W = []; i = st
        while True:
            W.append(W0[i]); i = nxt[i]
            if i == st: break
        assert len(W) == count
        Xs = [self.X_center(b, q) for b, q in W]
        ang = arb(0); n = len(Xs)
        for j in range(n):
            x = (Xs[j][0] - z[0], Xs[j][1] - z[1]); y = (Xs[(j + 1) % n][0] - z[0], Xs[(j + 1) % n][1] - z[1])
            ang += arb.atan2(det(x, y), x[0] * y[0] + x[1] * y[1])
        if not (abs(ang - 2 * PI) < 1): return None, 'winding'
        stats['drops'] = nd
        return W, 'ok'


def coefs(W):
    """area coefficients of a fan: F = 1/2 [C0 + sum_b det(U_b, t_b) + sum_{b<c} m_bc det(t_b, t_c)
       + sum_r cos r_r (A0_r + sum_b det(V_rb, t_b)) + sin r_r (B0_r + sum_b det(J V_rb, t_b)) + sum_pairs (Cc cos + Sc sin)]."""
    C0 = arb(0); A0 = {r: arb(0) for r in RB}; B0 = {r: arb(0) for r in RB}
    Cc = {pr: arb(0) for pr in PAIRS}; Sc = {pr: arb(0) for pr in PAIRS}
    U = {b: [arb(0), arb(0)] for b in TR}; Vr = {(r, b): [arb(0), arb(0)] for r in RB for b in TR}
    m = {(b, c): arb(0) for b in TR for c in TR if b < c}
    n = len(W)
    for j in range(n):
        bi, q = W[j]; bk, qq = W[(j + 1) % n]
        ri, rk = bi in ROT, bk in ROT
        dq = det(q, qq); dd = q[0] * qq[0] + q[1] * qq[1]
        if bi == bk or (not ri and not rk): C0 += dq
        elif not ri and rk: A0[bk] += dq; B0[bk] += dd
        elif ri and not rk: A0[bi] += dq; B0[bi] -= dd
        elif bi < bk: Cc[(bi, bk)] += dq; Sc[(bi, bk)] += dd
        else: Cc[(bk, bi)] += dq; Sc[(bk, bi)] -= dd
        if bk != 0:
            tgt = U[bk] if not ri else Vr[(bi, bk)]
            tgt[0] += q[0]; tgt[1] += q[1]
        if bi != 0:
            tgt = U[bi] if not rk else Vr[(bk, bi)]
            tgt[0] -= qq[0]; tgt[1] -= qq[1]
        if bi != 0 and bk != 0 and bi != bk:
            if bi < bk: m[(bi, bk)] += 1
            else: m[(bk, bi)] -= 1
    return dict(C0=C0, A0=A0, B0=B0, Cc=Cc, Sc=Sc, U=U, Vr=Vr, m=m)


def combine(cl, mus):
    out = dict(C0=arb(0), A0={r: arb(0) for r in RB}, B0={r: arb(0) for r in RB}, Cc={pr: arb(0) for pr in PAIRS},
               Sc={pr: arb(0) for pr in PAIRS}, U={b: [arb(0), arb(0)] for b in TR},
               Vr={(r, b): [arb(0), arb(0)] for r in RB for b in TR}, m={(b, c): arb(0) for b in TR for c in TR if b < c})
    for co, mu in zip(cl, mus):
        out['C0'] += mu * co['C0']
        for r in RB: out['A0'][r] += mu * co['A0'][r]; out['B0'][r] += mu * co['B0'][r]
        for pr in PAIRS: out['Cc'][pr] += mu * co['Cc'][pr]; out['Sc'][pr] += mu * co['Sc'][pr]
        for b in TR:
            out['U'][b][0] += mu * co['U'][b][0]; out['U'][b][1] += mu * co['U'][b][1]
        for k in out['Vr']:
            out['Vr'][k][0] += mu * co['Vr'][k][0]; out['Vr'][k][1] += mu * co['Vr'][k][1]
        for k in out['m']: out['m'][k] += mu * co['m'][k]
    return out


def area_min(bx, co, target=None):
    """minimum over the box of the (combined) fan area: 256 translation vertices x exact rotation minimum."""
    import itertools
    best = None
    for combo in itertools.product(*[bx.V[b] for b in (1, 2, 3, 4)]):
        T = dict(zip((1, 2, 3, 4), combo))
        K = co['C0'] + sum((det(co['U'][b], T[b]) for b in TR), arb(0))
        K += sum((co['m'][(b, c)] * det(T[b], T[c]) for (b, c) in co['m']), arb(0))
        A = {}; B = {}
        for r in RB:
            A[r] = co['A0'][r] + sum((det(co['Vr'][(r, b)], T[b]) for b in TR), arb(0))
            B[r] = co['B0'][r] + sum((det(J(co['Vr'][(r, b)]), T[b]) for b in TR), arb(0))
        v = tmin((K, A, B, dict(co['Cc']), dict(co['Sc'])), dict(bx.I), bx.cs, target=(None if target is None else 2 * target)) / 2
        best = v if best is None else amin(best, v)
    return best


def fan_area_at(W, p):
    """float fan area at parameter p (for tests)."""
    pl = {0: (0.0, (0.0, 0.0))}
    for b, (ix, iy) in TR.items(): pl[b] = (p[ROT[b]] if b in ROT else 0.0, (p[ix], p[iy]))
    X = []
    for b, q in W:
        r, t = pl[b]; c, s = math.cos(r), math.sin(r)
        X.append((c * float(q[0].mid()) - s * float(q[1].mid()) + t[0], s * float(q[0].mid()) + c * float(q[1].mid()) + t[1]))
    return 0.5 * sum(X[j][0] * X[(j + 1) % len(X)][1] - X[j][1] * X[(j + 1) % len(X)][0] for j in range(len(X)))


def wit_arb(p, eps):
    return [(b, (arb(q[0]), arb(q[1]))) for b, q in gen11.witnesses(list(p), eps=eps)]


def fan_for(bx, W0, stats, best_mode=False):
    """a fan valid on the box. First mode: the first valid fan over the centres z in ZC and both drop rules.
    Best mode: the first one without drops, else the one with the largest box minimum of its area."""
    for b, q in W0:
        if not member(b, q): return None, 'member'
    best = None; msg = 'no fan'
    for zf in ZC:
        z = (arb(zf[0]), arb(zf[1]))
        for rule in (0, 1):
            st = {}
            W, msg = bx.make_fan(W0, z, st, rule)
            if W is None: continue
            if st.get('drops', 0) == 0 or not best_mode:
                stats['drops'] = stats.get('drops', 0) + st.get('drops', 0)
                return W, 'ok'
            a = float(area_min(bx, coefs(W)).lower())
            if best is None or a > best[0]: best = (a, W, st.get('drops', 0))
    if best is None: return None, msg
    stats['drops'] = stats.get('drops', 0) + best[2]
    return best[1], 'ok'


def check_single(lo, hi, tau, eps, stats):
    bx = Box(lo, hi)
    W0 = wit_arb(bx.c, eps)
    for best_mode in (False, True):
        W, msg = fan_for(bx, W0, stats, best_mode)
        if W is None: return False, None, 'fan: ' + msg
        v = area_min(bx, coefs(W), float(tau.mid()))
        if v > tau: break
    return (v > tau), v, f'single wit={len(W)}'


def check_multi(lo, hi, tau, eps, shifts, lam, stats, Wlist=None):
    bx = Box(lo, hi)
    c = np.array(bx.c); h = 0.5 * (np.array(bx.hif) - np.array(bx.lof))
    lamf = [float(x) for x in lam]
    if any(not (x >= 0) for x in lamf) or not (sum(lamf) > 0): return False, None, 'bad weights', None
    la = [arb(x) for x in lamf]; tot = sum(la, arb(0)); mus = [x / tot for x in la]
    W0s = [None if lf == 0.0 else (Wlist[k] if Wlist is not None else wit_arb(c + np.asarray(sv, dtype=float) * h, eps))
           for k, (sv, lf) in enumerate(zip(shifts, lamf))]
    use = [mu for mu, lf in zip(mus, lamf) if lf != 0.0]
    for best_mode in (False, True):
        cl = []; ws = []
        for k, W0 in enumerate(W0s):
            if W0 is None: ws.append(None); continue
            W, msg = fan_for(bx, W0, stats, best_mode)
            if W is None: return False, None, f'structure {k} invalid: {msg}', None
            cl.append(coefs(W)); ws.append(W)
        v = area_min(bx, combine(cl, use), float(tau.mid()))
        if v > tau: break
    return (v > tau), v, f'multi k={len(cl)} wit={sum(len(w) for w in ws if w)}', ws


def check_leaf(code, lo, hi, tau, shifts=None, lam=None, depth=0, stats=None, Wlist=None):
    """returns (ok, min lower bound over the leaf, message); bisects on failure."""
    stats = {} if stats is None else stats
    tried = []
    for eps in (1e-8, 1e-10):
        if code == 253 and shifts is not None:
            ok, v, msg, ws = check_multi(lo, hi, tau, eps, shifts, lam, stats, Wlist)
            tried.append(msg)
            if ok: stats.setdefault('how', []).append(f'd{depth} multi eps={eps:g}'); return True, v, msg
            if Wlist is not None: Wlist = None
        ok, v, msg = check_single(lo, hi, tau, eps, stats)
        tried.append(msg)
        if ok: stats.setdefault('how', []).append(f'd{depth} single eps={eps:g}'); return True, v, msg
    if depth >= MAXD: return False, None, f'fail at depth {depth}: {tried}'
    scale = [1, 1, 0.5, 1, 1, 0.5, 1, 1, 0.5, 1, 1]
    k = int(np.argmax([(b - a) * s for a, b, s in zip(lo, hi, scale)]))
    mid = 0.5 * (lo[k] + hi[k])
    l1, h1 = list(lo), list(hi); h1[k] = mid; l2, h2 = list(lo), list(hi); l2[k] = mid
    stats['split'] = stats.get('split', 0) + 1
    ok1, v1, m1 = check_leaf(code, l1, h1, tau, shifts, lam, depth + 1, stats)
    if not ok1: return False, None, m1
    ok2, v2, m2 = check_leaf(code, l2, h2, tau, shifts, lam, depth + 1, stats)
    if not ok2: return False, None, m2
    return True, amin(v1, v2), f'split({m1}; {m2})'


if __name__ == '__main__':
    lv = np.load(sys.argv[1], allow_pickle=False)
    tau = arb(str(lv['tau_str']))
    out = open(sys.argv[2], 'a')
    idxs = [int(s) for s in sys.argv[3:]] if len(sys.argv) > 3 else range(len(lv['lo']))
    for i in idxs:
        t0 = time.time(); st = {}
        code = int(lv['code'][i]); ns = int(lv['nstruct'][i]); off = int(lv['soff'][i])
        sh = lv['shifts'][off:off + ns] if ns else None; lm = lv['lam'][off:off + ns] if ns else None
        ok, v, msg = check_leaf(code, list(lv['lo'][i]), list(lv['hi'][i]), tau, sh, lm, 0, st)
        rec = dict(idx=i, part=int(lv['part'][i]), pos=int(lv['pos'][i]), code=code, ok=bool(ok),
                   minbound=(v.str(15) if v is not None else None),
                   margin=(float((v - tau).lower()) if v is not None else None), msg=msg[:300], stats=st,
                   secs=round(time.time() - t0, 2))
        out.write(json.dumps(rec) + '\n'); out.flush()
        print(json.dumps(rec), flush=True)
