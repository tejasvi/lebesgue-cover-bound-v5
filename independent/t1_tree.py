"""Independent decoder of the certificate trees (D, B3, B5 and D, B3, B5, B7).

Reads part*.json / part*.npy (np.load, allow_pickle=False), rebuilds every leaf box with EXACT rational arithmetic
(fractions.Fraction from the float header values), using the semantics of lbcheck.py (DFS preorder, code < dim =
split at the midpoint of that coordinate, lower half first; 254 = bound leaf; 255 = far leaf), and checks:
  * structure: no truncation, no trailing data, all codes valid, all parts present with identical headers;
  * the float leaf boxes of lbcheck.py (midpoints m = 0.5*(l+h) in float; checked box c +- r with
    c = fl(0.5*(l+h)), r = fl(0.5*(h-l))) coincide EXACTLY with the rational boxes (no gaps);
  * the leaves tile the root box: sum of leaf volumes == root volume (exact).
Writes leaves.npz (float lo, hi, part, depth, code).
Usage: python -I t1_tree.py CERTDIR OUT.npz
"""
import sys, os, json
from fractions import Fraction as Fr
import numpy as np
if not __debug__:
    raise SystemExit('t1_tree.py uses assert statements; run it without -O')

certdir, out = sys.argv[1], sys.argv[2]
metas = {}
for f in sorted(os.listdir(certdir)):
    if f.startswith('part') and f.endswith('.json'):
        m = json.load(open(os.path.join(certdir, f)))
        metas[m['part']] = m
nparts = metas[0]['nparts']
assert sorted(metas) == list(range(nparts)), 'missing parts'
for k in ('ns', 'tau', 'split0', 'lo', 'hi', 'nparts'):
    assert all(metas[p][k] == metas[0][k] for p in metas), f'inconsistent header {k}'
m0 = metas[0]
dim = len(m0['lo'])
lo = [Fr(x) for x in m0['lo']]; hi = [Fr(x) for x in m0['hi']]; s0 = m0['split0']
root_vol = Fr(1)
for a, b in zip(lo, hi): root_vol *= (b - a)
cells = list(np.ndindex(*s0))
LO, HI, PART, DEPTH, CODE = [], [], [], [], []
vol = Fr(0)
mismatch = 0
float_mid_mismatch = 0
for p in range(nparts):
    codes = np.load(os.path.join(certdir, f'part{p:04d}.npy'), allow_pickle=False)
    pos = 0
    for cell in cells[p::nparts]:
        # rational cell bounds and the float bounds as lbcheck computes them
        cl = [lo[k] + (hi[k] - lo[k]) * cell[k] / s0[k] for k in range(dim)]
        ch = [lo[k] + (hi[k] - lo[k]) * (cell[k] + 1) / s0[k] for k in range(dim)]
        flo = np.array(m0['lo']); fhi = np.array(m0['hi']); fs0 = np.array(s0)
        fcl = flo + (fhi - flo) * np.array(cell) / fs0; fch = flo + (fhi - flo) * (np.array(cell) + 1) / fs0
        for k in range(dim):
            if Fr(float(fcl[k])) != cl[k] or Fr(float(fch[k])) != ch[k]:
                mismatch += 1
        stack = [(cl, ch, fcl.copy(), fch.copy(), 0)]
        while stack:
            l, h, fl, fh, dep = stack.pop()
            assert pos < len(codes), f'part {p}: truncated'
            code = int(codes[pos]); pos += 1
            if code in (254, 255):
                c = 0.5 * (fl + fh); r = 0.5 * (fh - fl)
                for k in range(dim):
                    if Fr(float(c[k] - r[k])) != l[k] or Fr(float(c[k] + r[k])) != h[k] or \
                       Fr(float(c[k])) - Fr(float(r[k])) != l[k] or Fr(float(c[k])) + Fr(float(r[k])) != h[k]:
                        mismatch += 1
                v = Fr(1)
                for k in range(dim): v *= (h[k] - l[k])
                vol += v
                LO.append([float(x) for x in l]); HI.append([float(x) for x in h]); PART.append(p); DEPTH.append(dep); CODE.append(code)
            elif 0 <= code < dim:
                mid = (l[code] + h[code]) / 2
                fmid = 0.5 * (fl[code] + fh[code])
                if Fr(float(fmid)) != mid: float_mid_mismatch += 1
                l2, h2 = list(l), list(h); l2[code] = mid
                l1, h1 = list(l), list(h); h1[code] = mid
                fl2, fh2 = fl.copy(), fh.copy(); fl2[code] = fmid
                fl1, fh1 = fl.copy(), fh.copy(); fh1[code] = fmid
                stack.append((l2, h2, fl2, fh2, dep + 1)); stack.append((l1, h1, fl1, fh1, dep + 1))
            else:
                raise SystemExit(f'part {p}: bad code {code}')
    assert pos == len(codes), f'part {p}: trailing data'
print(f'parts {nparts}, leaves {len(LO)} (bound {CODE.count(254)}, far {CODE.count(255)}), max depth {max(DEPTH)}')
print(f'float/rational mismatches in leaf boxes: {mismatch}; float midpoint mismatches: {float_mid_mismatch}')
print(f'sum of leaf volumes == root volume: {vol == root_vol}  ({float(vol)} vs {float(root_vol)})')
print('root lo', [float(x) for x in lo], 'hi', [float(x) for x in hi])
print('header values as exact dyadics: denominators', [Fr(x).denominator for x in m0['lo'] + m0['hi']])
np.savez(out, lo=np.array(LO), hi=np.array(HI), part=np.array(PART), depth=np.array(DEPTH), code=np.array(CODE))
