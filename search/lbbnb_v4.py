"""Branch and bound driver producing a certificate tree (search side, float).
Certificate per part: a numpy uint8 array in DFS preorder over the grid cells assigned to the part:
  0..dim-1 = internal node split along that coordinate (children: lower half first, then upper half),
  254 = leaf pruned by the fan/Taylor bound, 255 = leaf pruned by the corner far-field lemma.
Root domain is dyadic (outward-rounded), grid cells are dyadic (split0 = power of two per coordinate)."""
import numpy as np, sys, time, json, os
from lbsearch_v4 import Family, Rn

def dyadic_up(x, bits=24):
    return np.ceil(x*2**bits)/2**bits
def far_radius(tau):
    f = lambda d: 0.25*(np.pi - np.arccos(1/(2*d))) + 0.5*np.sqrt(d*d - 0.25)
    lo, hi = 0.5, 2.0
    for _ in range(200):
        m = 0.5*(lo + hi)
        if f(m) >= tau: hi = m
        else: lo = m
    return hi
def tmax(n, tau):
    d = far_radius(tau); R = Rn(n); c = np.cos(np.pi/n)
    return -R*c + np.sqrt((R*c)**2 - (R*R - d*d))
def root_domain(ns, tau):
    T = [dyadic_up(tmax(n, tau) + 1e-9) for n in ns]
    lo = [-T[0], -T[0]]; hi = [T[0], T[0]]
    for i, n in enumerate(ns[1:], start=1):
        lo += [0.0, -T[i], -T[i]]
        hi += [dyadic_up((np.pi/n if i == 1 else 2*np.pi/n) + 1e-12), T[i], T[i]]
    return np.array(lo), np.array(hi), T

def run(ns, tau, delta, part, nparts, split0, N=1024, eps=1e-6, outdir='cert', maxboxes=10**12, use_multi=True):
    fam = Family(ns, N=N, eps=eps)
    lo, hi, T = root_domain(ns, tau)
    d = fam.dim
    tidx = [(0, 1)] + [(2 + 3*(i-1) + 1, 2 + 3*(i-1) + 2) for i in range(1, len(ns))]
    s0 = np.array(split0)
    cells = list(np.ndindex(*split0))[part::nparts]
    rec = bytearray(); nbox = 0; nfar = 0; nbnd = 0; nmul = 0; side = []; minL = np.inf; t0 = time.time()
    tau_s = tau + delta
    def minnorm(l, h, a, b):
        x = 0.0 if l[a] <= 0 <= h[a] else min(abs(l[a]), abs(h[a]))
        y = 0.0 if l[b] <= 0 <= h[b] else min(abs(l[b]), abs(h[b]))
        return np.hypot(x, y)
    for cell in cells:
        cl = lo + (hi - lo)*np.array(cell)/s0; ch = lo + (hi - lo)*(np.array(cell) + 1)/s0
        stack = [(cl, ch)]
        while stack:
            l, h = stack.pop(); nbox += 1
            if any(minnorm(l, h, a, b) > T[i]*(1 - 1e-12) for i, (a, b) in enumerate(tidx)):
                rec.append(255); nfar += 1; continue
            c = 0.5*(l + h); hw = 0.5*(h - l)
            L, info = fam.bound2(c, hw, tau_s)
            if L >= tau_s:
                rec.append(254); nbnd += 1; minL = min(minL, L); continue
            if use_multi and info is not None and info['F'] - 1.5*info['e2'] > tau_s:
                Lm, im = fam.bound_multi(c, hw)
                if Lm >= tau_s and 'multi' in im:
                    rec.append(253); nmul += 1; minL = min(minL, Lm)
                    mm_, lamv, used = im['multi']
                    side.append((len(rec) - 1, used, lamv)); continue
            if hw.max() < 1e-9:
                raise RuntimeError(f'stuck at {list(c)} L={L}')
            wts = np.ones(d)
            if info is None: k = int(np.argmax(hw))
            else: k = int(np.argmax(info['contrib'] + 1e-15*hw))
            rec.append(k)
            m = 0.5*(l[k] + h[k])
            l2, h2 = l.copy(), h.copy(); l2[k] = m      # upper half pushed first -> popped second
            l1, h1 = l.copy(), h.copy(); h1[k] = m
            stack.append((l2, h2)); stack.append((l1, h1))
            if nbox % 20000 == 0:
                print(f'  part {part}: boxes {nbox} far {nfar} bnd {nbnd} multi {nmul} {time.time()-t0:.0f}s', flush=True)
    os.makedirs(outdir, exist_ok=True)
    np.save(os.path.join(outdir, f'part{part:04d}.npy'), np.frombuffer(bytes(rec), dtype=np.uint8))
    if side:
        np.savez(os.path.join(outdir, f'part{part:04d}_multi.npz'),
                 pos=np.array([s_[0] for s_ in side], dtype=np.int64),
                 nstruct=np.array([len(s_[1]) for s_ in side], dtype=np.int64),
                 shifts=np.concatenate([s_[1] for s_ in side]).astype(np.int8),
                 lam=np.concatenate([s_[2] for s_ in side]).astype(np.float64))
    meta = dict(ns=ns, tau=tau, delta=delta, part=part, nparts=nparts, split0=list(split0), N=N, eps=eps,
                lo=lo.tolist(), hi=hi.tolist(), T=T, boxes=nbox, far=nfar, bnd=nbnd, multi=nmul, minL=minL, secs=time.time()-t0)
    json.dump(meta, open(os.path.join(outdir, f'part{part:04d}.json'), 'w'))
    return meta

if __name__ == '__main__':
    ns = [int(v) for v in sys.argv[1].split(',')]
    tau = float(sys.argv[2]); delta = float(sys.argv[3]); part = int(sys.argv[4]); nparts = int(sys.argv[5])
    split0 = [int(v) for v in sys.argv[6].split(',')]
    outdir = sys.argv[7]
    N = int(sys.argv[8]) if len(sys.argv) > 8 else 1024
    m = run(ns, tau, delta, part, nparts, split0, N=N, outdir=outdir)
    print(json.dumps({k: m[k] for k in ('part', 'boxes', 'far', 'bnd', 'multi', 'minL', 'secs')}), flush=True)
