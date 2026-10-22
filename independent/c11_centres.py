"""Hull area (gen8 support-function code with B9) at every leaf centre of the 11D certificate, parts FIRST..LAST-1.
Writes one JSON line per part: number of leaves, smallest area, its leaf centre.
Usage: python -I c11_centres.py CERTDIR FIRST LAST OUT.jsonl"""
import sys, os, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen11
SRC = sys.argv[1]
first, last, out = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
meta = json.load(open(f'{SRC}/part0000.json')); lo = np.array(meta['lo']); hi = np.array(meta['hi']); s0 = np.array(meta['split0'])
cells = list(np.ndindex(*meta['split0']))
with open(out, 'a') as fh:
    for part in range(first, last):
        codes = np.load(f'{SRC}/part{part:04d}.npy'); pos = 0; n = 0; best = (9.0, None)
        for c_ in cells[part::meta['nparts']]:
            stack = [(lo + (hi - lo)*np.array(c_)/s0, lo + (hi - lo)*(np.array(c_) + 1)/s0)]
            while stack:
                l, h = stack.pop(); code = int(codes[pos]); pos += 1
                if code >= 253:
                    c = 0.5*(l + h); a = gen11.area(list(c)); n += 1
                    if a < best[0]: best = (a, c.tolist())
                else:
                    mid = 0.5*(l[code] + h[code]); l2, h2 = l.copy(), h.copy(); l2[code] = mid; l1, h1 = l.copy(), h.copy(); h1[code] = mid
                    stack.append((l2, h2)); stack.append((l1, h1))
        fh.write(json.dumps(dict(part=part, leaves=n, min_area=best[0], centre=best[1])) + '\n'); fh.flush()
