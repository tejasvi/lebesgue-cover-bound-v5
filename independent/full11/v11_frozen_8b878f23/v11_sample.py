"""v11_sample.py CERTDIR DECODE.json SEED N254 N253 OUT.npz [TARGETS.json]: draw a seeded uniform random sample of
code-254 and code-253 leaves (global ranks without replacement, numpy default_rng(SEED)), add all far leaves (255)
and the targeted leaves [[part, pos, tag], ...], decode their exact boxes and side data with treedec11, write OUT.npz."""
import sys, os, json
sys.dont_write_bytecode = True
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import treedec11
certdir, dec, seed, n254, n253, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
targets = json.load(open(sys.argv[7])) if len(sys.argv) > 7 else []
parts = json.load(open(dec))['parts']
rng = np.random.default_rng(seed)
want = {}
tags = {}
for code, n in ((254, n254), (253, n253)):
    cnt = np.array([p['counts'][str(code)] for p in parts], dtype=np.int64); cum = np.concatenate([[0], np.cumsum(cnt)])
    g = rng.choice(int(cum[-1]), size=n, replace=False)
    for r in sorted(g.tolist()):
        pi = int(np.searchsorted(cum, r, side='right') - 1)
        want.setdefault(pi, {}).setdefault(code, set()).add(int(r - cum[pi])); tags[(pi, code, int(r - cum[pi]))] = f'uniform{code}'
for pi, p in enumerate(parts):
    if p['counts']['255']:
        want.setdefault(pi, {}).setdefault(255, set()).update(range(p['counts']['255']))
        for r in range(p['counts']['255']): tags[(pi, 255, r)] = 'far'
for part, pos, tag in targets:
    want.setdefault(part, {}).setdefault('pos', set()).add(pos); tags[(part, 'pos', pos)] = tag
rows = []
for pi in sorted(want):
    s, leaves = treedec11.decode_part(certdir, pi, want[pi])
    assert not s['errs'], s['errs']
    for (code, pos, lo, hi, rank, side) in leaves:
        tg = []
        if (pi, code, rank) in tags: tg.append(tags[(pi, code, rank)])
        if (pi, 'pos', pos) in tags: tg.append(tags[(pi, 'pos', pos)])
        rows.append((pi, pos, code, rank, lo, hi, side, '+'.join(tg)))
shifts = []; lam = []; soff = []; nst = []
for r in rows:
    soff.append(len(lam))
    if r[6] is None: nst.append(0); continue
    shifts.extend(r[6][0]); lam.extend(r[6][1]); nst.append(len(r[6][1]))
meta = json.load(open(os.path.join(certdir, 'part0000.json')))
np.savez(out, part=np.array([r[0] for r in rows]), pos=np.array([r[1] for r in rows]), code=np.array([r[2] for r in rows]),
         rank=np.array([r[3] for r in rows]), lo=np.array([r[4] for r in rows]), hi=np.array([r[5] for r in rows]),
         tag=np.array([r[7] for r in rows]), soff=np.array(soff), nstruct=np.array(nst),
         shifts=np.array(shifts, dtype=float).reshape(-1, 11), lam=np.array(lam, dtype=float), tau_str=np.array(repr(float(meta['tau']))),
         seed=np.array(seed))
from collections import Counter
print(out, len(rows), 'leaves;', Counter(r[7] for r in rows), Counter(r[2] for r in rows))
