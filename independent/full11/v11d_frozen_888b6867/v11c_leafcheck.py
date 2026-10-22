"""V11d = V11c with one fix: when the LP has converged below tau, a new structure is added at the minimiser (v11c
stopped there instead). V11c (audit, third pass for the leaves that v11 and v11b did not verify): Lemma K with MY OWN structure points and
weights. For a leaf box:
  * structures: fans built from the exact hull at points of the box (the record's shift points as first hints, the box
    centre, then the minimisers of the current combination), witness lists filtered as in v11b (thr = 1e-5), every fan
    verified on the whole box (v11b fan_for);
  * weights: cutting-plane linear programme (scipy linprog/HiGHS): maximise t subject to sum_i mu_i F_i(p) >= t at the
    current point set, mu >= 0, sum mu = 1; the minimiser p* of sum mu_i F_i over the box (float search over the 256
    translation vertices x rotations) is added, a new structure is built at p*, and the loop repeats;
  * verdict: the exact box minimum (v11b area_min, arb) of sum mu_i F_i with mu normalised in arb exceeds tau; the LP
    and the float searches only choose mu and the points (any choice is admissible).
  * bisection (depth <= MAXD) if the loop does not reach tau.
"""
import sys, os, math, itertools
sys.dont_write_bytecode = True
import numpy as np
from scipy.optimize import linprog, minimize
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import v11b_leafcheck as B
from flint import arb
MAXD = 5
ITERS = 25
THR = 1e-5


def co_float(co):
    f = lambda x: float(x.mid())
    return dict(C0=f(co['C0']), A0={r: f(v) for r, v in co['A0'].items()}, B0={r: f(v) for r, v in co['B0'].items()},
                Cc={k: f(v) for k, v in co['Cc'].items()}, Sc={k: f(v) for k, v in co['Sc'].items()},
                U={b: (f(v[0]), f(v[1])) for b, v in co['U'].items()}, Vr={k: (f(v[0]), f(v[1])) for k, v in co['Vr'].items()},
                m={k: f(v) for k, v in co['m'].items()})


def eval_cf(cf, p):
    """fan area at p from float coefficients."""
    T = {b: (p[ix], p[iy]) for b, (ix, iy) in B.TR.items()}
    d = lambda a, t: a[0] * t[1] - a[1] * t[0]
    v = cf['C0'] + sum(d(cf['U'][b], T[b]) for b in B.TR) + sum(cf['m'][(b, c)] * d(T[b], T[c]) for (b, c) in cf['m'])
    for r in B.RB:
        Ar = cf['A0'][r] + sum(d(cf['Vr'][(r, b)], T[b]) for b in B.TR)
        Br = cf['B0'][r] + sum(d((-cf['Vr'][(r, b)][1], cf['Vr'][(r, b)][0]), T[b]) for b in B.TR)
        v += Ar * math.cos(p[B.ROT[r]]) + Br * math.sin(p[B.ROT[r]])
    for (x, y) in B.PAIRS:
        dr = p[B.ROT[y]] - p[B.ROT[x]]; v += cf['Cc'][(x, y)] * math.cos(dr) + cf['Sc'][(x, y)] * math.sin(dr)
    return 0.5 * v


def comb_argmin(cfs, mu, lo, hi):
    """float minimiser of sum mu_i F_i over the box: each translation vertex, rotations by L-BFGS-B from corners."""
    best = (math.inf, None)
    rot = [B.ROT[r] for r in B.RB]
    for combo in itertools.product((0, 1), repeat=8):
        p = 0.5 * (np.array(lo) + np.array(hi))
        for k, (b, (ix, iy)) in enumerate(B.TR.items()):
            p[ix] = lo[ix] if combo[2 * k] == 0 else hi[ix]; p[iy] = lo[iy] if combo[2 * k + 1] == 0 else hi[iy]
        def g(x):
            q = p.copy(); q[rot] = x
            return sum(m * eval_cf(cf, q) for m, cf in zip(mu, cfs))
        x0 = min(itertools.product(*[(lo[j], hi[j]) for j in rot]), key=lambda x: g(np.array(x)))
        r = minimize(g, np.array(x0), method='L-BFGS-B', bounds=[(lo[j], hi[j]) for j in rot])
        if r.fun < best[0]:
            q = p.copy(); q[rot] = r.x; best = (r.fun, q)
    return best


def lp_weights(Fmat):
    """max t s.t. Fmat @ mu >= t, mu >= 0, sum mu = 1 (Fmat: points x structures)."""
    npt, m = Fmat.shape
    c = np.zeros(m + 1); c[-1] = -1.0
    A = np.hstack([-Fmat, np.ones((npt, 1))]); b = np.zeros(npt)
    Aeq = np.zeros((1, m + 1)); Aeq[0, :m] = 1.0
    r = linprog(c, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=[1.0], bounds=[(0, None)] * m + [(None, None)], method='highs')
    if r.status != 0: return None, None
    return np.maximum(r.x[:m], 0.0), r.x[-1]


def check_own_lemma_k(lo, hi, tau, shifts, stats):
    bx = B.Box(lo, hi); c = np.array(bx.c); h = 0.5 * (np.array(bx.hif) - np.array(bx.lof))
    taf = float(tau.mid())
    pts0 = [c + np.asarray(s, dtype=float) * h for s in (shifts if shifts is not None else [])] + [c]
    cls, cfs = [], []
    def add_structure(p):
        W, msg = B.fan_for(bx, B.wit_arb(list(p), 1e-8, THR), stats, False)
        if W is None: return False
        co = B.coefs(W); cls.append(co); cfs.append(co_float(co)); return True
    for p in pts0: add_structure(p)
    if not cls: return False, None, 'no valid structure'
    P = [np.where(np.array(bits) == 0, np.array(lo), np.array(hi)) for bits in itertools.product((0, 1), repeat=11)][::8] + pts0
    best_v = None
    for it in range(ITERS):
        Fmat = np.array([[eval_cf(cf, p) for cf in cfs] for p in P])
        mu, t = lp_weights(Fmat)
        if mu is None: return False, None, 'lp failed'
        val, pstar = comb_argmin(cfs, mu, lo, hi)
        stats['lp_iters'] = it + 1
        if val >= t - 1e-10 or it == ITERS - 1 or val > taf + 1e-7:
            use = [i for i in range(len(cls)) if mu[i] > 0]
            ma = [arb(float(mu[i])) for i in use]; tot = sum(ma, arb(0)); ma = [x / tot for x in ma]
            v = B.area_min(bx, B.combine([cls[i] for i in use], ma), taf)
            best_v = v
            if v > tau: return True, v, f'own lemma K: {len(use)} of {len(cls)} structures, {it + 1} LP rounds'
        P.append(pstar)
        if not add_structure(pstar) and val >= t - 1e-10:
            break                                               # converged, and no new structure at the minimiser
    return False, best_v, f'own lemma K short: {len(cls)} structures'


def check_leaf_c(lo, hi, tau, shifts=None, depth=0, stats=None):
    stats = {} if stats is None else stats
    ok, v, msg = check_own_lemma_k(lo, hi, tau, shifts, stats)
    if ok:
        stats.setdefault('how', []).append(f'd{depth} ownK'); return True, v, msg
    if depth >= MAXD: return False, None, f'fail at depth {depth}: {msg}'
    scale = [1, 1, 0.5, 1, 1, 0.5, 1, 1, 0.5, 1, 1]
    k = int(np.argmax([(b - a) * s for a, b, s in zip(lo, hi, scale)]))
    mid = 0.5 * (lo[k] + hi[k])
    l1, h1 = list(lo), list(hi); h1[k] = mid; l2, h2 = list(lo), list(hi); l2[k] = mid
    stats['split'] = stats.get('split', 0) + 1
    out = []
    for (l, hh) in ((l1, h1), (l2, h2)):
        ok, v, m = check_leaf_c(l, hh, tau, shifts, depth + 1, stats)
        if not ok: return False, None, m
        out.append(v)
    return True, B.amin(out[0], out[1]), 'split'


if __name__ == '__main__':
    import json, time
    with np.load(sys.argv[1]) as z: lv = {k: z[k] for k in z.files}
    tau = arb(str(lv['tau_str']))
    for s in sys.argv[3:]:
        i = int(s); t0 = time.time(); st = {}
        ns = int(lv['nstruct'][i]); off = int(lv['soff'][i]); sh = lv['shifts'][off:off + ns] if ns else None
        ok, v, msg = check_leaf_c(list(lv['lo'][i]), list(lv['hi'][i]), tau, sh, 0, st)
        rec = dict(idx=i, part=int(lv['part'][i]), pos=int(lv['pos'][i]), code=int(lv['code'][i]), ok=bool(ok),
                   minbound=(v.str(15) if v is not None else None), margin=(float((v - tau).lower()) if v is not None else None),
                   msg=msg[:300], stats=st, secs=round(time.time() - t0, 2))
        print(json.dumps(rec), flush=True)
        open(sys.argv[2], 'a').write(json.dumps(rec) + '\n')
