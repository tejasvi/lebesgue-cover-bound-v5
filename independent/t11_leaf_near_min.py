"""Negative test: the certificate leaf that contains a numerical minimizer x* of the five-body hull area must pass the
checker at the certificate's tau = 0.8366 and fail at a target above A(x*). Uses the checker's own leaf routines.
Usage: python -I t11_leaf_near_min.py CERTDIR X_JSON TAU_HIGH"""
import sys, os, json, importlib.util
import numpy as np
CHK = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'checker', 'lbcheck.py')
SRC = sys.argv[1]
spec = importlib.util.spec_from_file_location('lbcheck_v4', CHK); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
x = np.array(json.load(open(sys.argv[2])), dtype=float); tau_hi = float(sys.argv[3])
meta = json.load(open(f'{SRC}/part0000.json')); lo = np.array(meta['lo']); hi = np.array(meta['hi']); s0 = np.array(meta['split0'])
x[[2, 5, 8]] = np.mod(x[[2, 5, 8]], [2*np.pi/5, 2*np.pi/7, 2*np.pi/9])      # periodicity of rho_2..rho_4 (Lemma 2.3)
assert np.all(lo <= x) and np.all(x <= hi), x
cell = tuple(int(v) for v in np.minimum(((x - lo)/(hi - lo)*s0).astype(int), s0 - 1))
cells = list(np.ndindex(*meta['split0'])); part = cells.index(cell) % meta['nparts']
codes = np.load(f'{SRC}/part{part:04d}.npy'); z = np.load(f'{SRC}/part{part:04d}_multi.npz')
side = {}; off = 0
for p_, n_ in zip(z['pos'], z['nstruct']): side[int(p_)] = (z['shifts'][off:off + n_], z['lam'][off:off + n_]); off += int(n_)
pos = 0; found = None
for c_ in cells[part::meta['nparts']]:
    stack = [(lo + (hi - lo)*np.array(c_)/s0, lo + (hi - lo)*(np.array(c_) + 1)/s0)]
    while stack:
        l, h = stack.pop(); code = int(codes[pos]); pos += 1
        inside = np.all(l <= x) and np.all(x <= h)
        if code >= 253:
            if inside and found is None: found = (code, l.copy(), h.copy(), pos - 1)
        else:
            mid = 0.5*(l[code] + h[code]); l2, h2 = l.copy(), h.copy(); l2[code] = mid; l1, h1 = l.copy(), h.copy(); h1[code] = mid
            stack.append((l2, h2)); stack.append((l1, h1))
code, l, h, node = found
c, w = 0.5*(l + h), 0.5*(h - l)
print(f'part {part}, node {node}, code {code}, half-widths {np.round(w, 8).tolist()}')
for tau in (meta['tau'], tau_hi):
    ch = m.Checker(meta['ns'], tau, meta['N'], meta['eps'])
    if code == 254: ok, msg = ch.check_bound_leaf(c, w)
    elif code == 253: ok, msg = ch.check_multi_leaf(c, w, *side[node])
    else: ok, msg = ch.check_far_leaf(l, h, meta['T']), 'far'
    print(f'tau = {tau}: accepted = {ok} ({msg})', flush=True)
