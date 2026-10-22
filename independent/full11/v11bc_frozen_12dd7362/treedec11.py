"""treedec11.py (audit): independent decoder of the 11D covering record, exact integer/rational boxes.

Format as described in lebesgue13b/PROGRESS.md (DFS preorder codes, lower child first; code-253 side data in the
Lemma K entry). I have also read lbcheck_v4's check_part, so this is a re-implementation, not a blind one: it decodes
with exact integer boxes and adds checks that lbcheck_v4 does not make (volume sum, binary64 end points, side-data
positions equal to the 253 nodes in order). Format:
  part p owns the root cells ndindex(split0)[p::nparts] of the header box [lo, hi] (cell k spans
  lo + (hi - lo) * k / split0 .. lo + (hi - lo) * (k + 1) / split0 per coordinate);
  each root cell is followed in the code stream by its subtree in preorder: a code 0..dim-1 bisects that coordinate
  and is followed by the lower half's subtree, then the upper half's; 253 / 254 / 255 are leaves (Lemma K / fan / far);
  the _multi.npz side data (pos, nstruct, shifts, lam) belongs to the code-253 nodes.
Checks per part: valid codes; the stream is consumed exactly; side-data positions are exactly the 253 nodes (strictly
increasing), nstruct >= 1, array lengths consistent, all values finite, lam >= 0 with a positive sum; every root-cell
corner, split midpoint and leaf end point is a binary64 number (so a decoder that bisects in floating point with
0.5*(l + h) gets exactly these boxes); the leaf volumes add up to the root cell volume (exact integers).
Checks over all parts: identical header fields; the parts' root cells are distinct and cover the split0 grid.
Usage: treedec11.py CERTDIR WORKERS OUT.json
"""
import sys, os, json, math
sys.dont_write_bytecode = True
import numpy as np
from fractions import Fraction

D = 64                                          # integer resolution per coordinate: positions a / 2^D of the root cell


def is_double(fr):
    """exact test: the rational fr is a binary64 number (normal range suffices here)."""
    if fr == 0: return True
    n, d = abs(fr.numerator), fr.denominator
    if d & (d - 1): return False                # denominator must be a power of two
    tz = (n & -n).bit_length() - 1
    return (n >> tz).bit_length() <= 53


def root_cells(meta):
    lo = [Fraction(x) for x in meta['lo']]; hi = [Fraction(x) for x in meta['hi']]; s0 = meta['split0']
    cells = list(np.ndindex(*s0))[meta['part']::meta['nparts']]
    out = []
    for cell in cells:
        L = [lo[k] + (hi[k] - lo[k]) * cell[k] / s0[k] for k in range(len(lo))]
        H = [lo[k] + (hi[k] - lo[k]) * (cell[k] + 1) / s0[k] for k in range(len(lo))]
        out.append((tuple(int(c) for c in cell), L, H))
    return out


def decode_part(certdir, part, want=None):
    """returns (summary dict, leaves) where leaves lists (code, pos, lo floats, hi floats, side) for the code ranks in
    want = {code: set of ranks within that code} (None: no leaves returned)."""
    meta = json.load(open(os.path.join(certdir, f'part{part:04d}.json')))
    codes = np.load(os.path.join(certdir, f'part{part:04d}.npy'), allow_pickle=False)
    dim = 2 + 3 * (len(meta['ns']) - 1)
    errs = []
    if codes.dtype != np.uint8: errs.append(f'codes dtype {codes.dtype}')
    cl = codes.tolist()
    side = None
    mf = os.path.join(certdir, f'part{part:04d}_multi.npz')
    if os.path.exists(mf):
        z = np.load(mf, allow_pickle=False)
        if sorted(z.files) != ['lam', 'nstruct', 'pos', 'shifts']: errs.append(f'npz keys {sorted(z.files)}')
        zpos, zns, zsh, zlam = z['pos'], z['nstruct'], z['shifts'], z['lam']
        side = (zpos, zns, zsh, zlam)
    counts = {253: 0, 254: 0, 255: 0}; nsplit = 0; maxdepth = [0] * dim
    pos253 = []; vol = 0; leaves = []; rank = {253: 0, 254: 0, 255: 0}
    nondouble = 0; minw = [None] * dim
    pos = 0
    for cell, L, H in root_cells(meta):
        W = [H[k] - L[k] for k in range(dim)]
        for k in range(dim):
            if not (is_double(L[k]) and is_double(H[k])): nondouble += 1
        stack = [((0,) * dim, (1 << D,) * dim, (0,) * dim)]
        while stack:
            a, b, dep = stack.pop()
            if pos >= len(cl): errs.append('stream truncated'); stack = []; break
            code = cl[pos]; pos += 1
            if code < dim:
                k = code
                if (a[k] + b[k]) & 1: errs.append('resolution exceeded'); continue
                m = (a[k] + b[k]) >> 1
                mid = L[k] + W[k] * Fraction(m, 1 << D)
                if not is_double(mid): nondouble += 1
                a2 = list(a); a2[k] = m; b1 = list(b); b1[k] = m; d2 = list(dep); d2[k] += 1
                if d2[k] > maxdepth[k]: maxdepth[k] = d2[k]
                stack.append((tuple(a2), b, tuple(d2)))     # upper half: decoded after the lower half
                stack.append((a, tuple(b1), tuple(d2)))     # lower half: next in the stream
                nsplit += 1
            elif code in (253, 254, 255):
                counts[code] += 1
                v = 1
                for k in range(dim): v *= (b[k] - a[k])
                vol += v
                if code == 253: pos253.append(pos - 1)
                for k in range(dim):
                    w = W[k] * Fraction(b[k] - a[k], 1 << D)
                    if minw[k] is None or w < minw[k]: minw[k] = w
                if want is not None and (want == 'all' or rank[code] in want.get(code, ()) or (pos - 1) in want.get('pos', ())):
                    lo = [float(L[k] + W[k] * Fraction(a[k], 1 << D)) for k in range(dim)]
                    hi = [float(L[k] + W[k] * Fraction(b[k], 1 << D)) for k in range(dim)]
                    leaves.append((code, pos - 1, lo, hi, rank[code]))
                rank[code] += 1
            else:
                errs.append(f'bad code {code} at {pos - 1}'); stack = []; break
        if vol != 0 and False: pass
    ncells = len(root_cells(meta))
    if pos != len(cl): errs.append(f'trailing data: used {pos} of {len(cl)}')
    if vol != ncells * (1 << (D * dim)): errs.append('leaf volumes do not add up to the root cells')
    sidechk = {}
    if counts[253]:
        if side is None: errs.append('253 leaves without side data')
        else:
            zpos, zns, zsh, zlam = side
            if zpos.tolist() != pos253: errs.append('side-data positions differ from the 253 nodes (or not increasing)')
            if len(zns) != len(zpos) or int(zns.min()) < 1: errs.append('nstruct')
            tot = int(zns.sum())
            if zsh.shape != (tot, dim) or zlam.shape != (tot,): errs.append(f'side shapes {zsh.shape} {zlam.shape} vs {tot}')
            if not (np.isfinite(zsh).all() and np.isfinite(zlam).all()): errs.append('non-finite side data')
            if (zlam < 0).any(): errs.append('negative lam')
            off = np.concatenate([[0], np.cumsum(zns)])
            sums = np.add.reduceat(zlam, off[:-1]) if len(zns) else np.array([])
            if (sums <= 0).any(): errs.append('lam sum <= 0')
            sidechk = dict(nstruct_min=int(zns.min()), nstruct_max=int(zns.max()), nstruct_mean=float(zns.mean()),
                           shift_min=float(zsh.min()), shift_max=float(zsh.max()), zero_lam=int((zlam == 0).sum()))
            if want is not None:
                idx = {p: i for i, p in enumerate(pos253)}
                leaves = [(c, p, lo, hi, r, (zsh[off[idx[p]]:off[idx[p] + 1]].tolist(), zlam[off[idx[p]]:off[idx[p] + 1]].tolist()) if c == 253 else None)
                          for (c, p, lo, hi, r) in leaves]
    elif side is not None and len(side[0]): errs.append('side data without 253 leaves')
    if want is not None and counts[253] == 0:
        leaves = [(c, p, lo, hi, r, None) for (c, p, lo, hi, r) in leaves]
    summ = dict(part=part, cells=[c for c, _, _ in root_cells(meta)], counts={str(k): v for k, v in counts.items()},
                nodes=len(cl), splits=nsplit, maxdepth=maxdepth, nondouble=nondouble, minwidth=[float(x) for x in minw],
                side=sidechk, errs=errs,
                header={k: meta[k] for k in ('ns', 'tau', 'split0', 'lo', 'hi', 'nparts')})
    return summ, leaves


def _work(args):
    certdir, part = args
    s, _ = decode_part(certdir, part)
    return s


if __name__ == '__main__':
    certdir, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    names = sorted(f for f in os.listdir(certdir) if f.startswith('part') and f.endswith('.json'))
    m0 = json.load(open(os.path.join(certdir, names[0])))
    nparts = m0['nparts']
    assert names == [f'part{p:04d}.json' for p in range(nparts)], 'part files are not exactly part0000..'
    import multiprocessing as mp
    with mp.get_context('fork').Pool(workers) as pool:
        res = pool.map(_work, [(certdir, p) for p in range(nparts)], chunksize=4)
    errs = [(r['part'], r['errs']) for r in res if r['errs']]
    h0 = res[0]['header']
    hdr_bad = [r['part'] for r in res if r['header'] != h0]
    cells = [tuple(c) for r in res for c in r['cells']]
    grid = set(np.ndindex(*h0['split0']))
    tot = {k: sum(r['counts'][k] for r in res) for k in ('253', '254', '255')}
    summary = dict(parts=len(res), header=h0, header_mismatch=hdr_bad, cells=len(cells), distinct_cells=len(set(cells)),
                   grid_cells=len(grid), cover_ok=(set(cells) == grid and len(cells) == len(grid)),
                   leaves=sum(tot.values()), counts=tot, nodes=sum(r['nodes'] for r in res),
                   maxdepth=[max(r['maxdepth'][k] for r in res) for k in range(len(res[0]['maxdepth']))],
                   nondouble=sum(r['nondouble'] for r in res),
                   minwidth=[min(r['minwidth'][k] for r in res) for k in range(len(res[0]['minwidth']))],
                   nstruct_max=max((r['side'].get('nstruct_max', 0) for r in res)),
                   shift_range=[min((r['side'].get('shift_min', 0) for r in res)), max((r['side'].get('shift_max', 0) for r in res))],
                   zero_lam=sum(r['side'].get('zero_lam', 0) for r in res),
                   parts_with_errors=len(errs), first_errors=errs[:10])
    json.dump(dict(summary=summary, parts=res), open(out, 'w'))
    print(json.dumps(summary, indent=1))
