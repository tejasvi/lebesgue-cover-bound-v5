"""Exact decoder of the certificate trees (standard library and numpy only; it does not import lbcheck.py).

For every part it rebuilds the boxes of the tree in exact rational arithmetic from the header values, with the
semantics of lbcheck.py: the root box [lo, hi] is cut into the grid split0, part j holds the cells
list(numpy.ndindex(*split0))[j::nparts]; each cell is traversed in depth-first preorder; a code k < dim splits the box
at the midpoint of coordinate k (lower half first), 253 is a leaf closed by a convex combination of fan bounds (its
data are in the file part####_multi.npz), 254 a leaf closed by the fan bound and 255 a leaf closed by the corner
lemma.  It also repeats the double-precision computations of lbcheck.py and checks that the box c +- h that
lbcheck.py verifies at each leaf (c = fl((l + h)/2), h = fl((h - l)/2)) equals the exact leaf box.  It checks that
all parts are present with identical headers, that no part is truncated or has trailing data, that the leaf volumes
of every grid cell add up to the volume of the cell (each split halves a box, so this is the identity
sum over the leaves of 2^-depth = 1), and that the side file of a part lists exactly its nodes with
code 253.
Usage: python3 treecheck.py CERTDIR [FIRST LAST]    checks the parts FIRST, ..., LAST-1 (default: all parts)
       python3 treecheck.py --combine OUTPUT...     adds up the outputs of runs over disjoint ranges of parts"""
import sys, os, json
from fractions import Fraction as Fr
import numpy as np

HEAD = ('ns', 'tau', 'split0', 'lo', 'hi', 'nparts')


def headers(certdir):
    metas = {}
    for f in sorted(os.listdir(certdir)):
        if f.startswith('part') and f.endswith('.json'):
            with open(os.path.join(certdir, f)) as fh:
                m = json.load(fh)
            metas[m['part']] = m
    return metas


def side_ok(certdir, p, codes):
    """the side file lists exactly the nodes with code 253, with well-formed sign vectors and weights."""
    multi = set(int(i) for i in np.nonzero(codes == 253)[0])
    mf = os.path.join(certdir, f'part{p:04d}_multi.npz')
    if not os.path.exists(mf):
        return not multi
    z = np.load(mf, allow_pickle=False)
    pos, ns_, sh, lam = z['pos'], z['nstruct'], z['shifts'], z['lam']
    if len(pos) != len(ns_) or int(ns_.sum()) != len(sh) or len(sh) != len(lam) or (len(ns_) and ns_.min() < 1):
        return False
    if sh.size and (sh.min() < -1 or sh.max() > 1):
        return False
    return set(int(i) for i in pos) == multi and len(set(int(i) for i in pos)) == len(pos)


def main(certdir, first=None, last=None):
    metas = headers(certdir)
    m0 = metas[min(metas)]
    nparts = m0['nparts']
    if sorted(metas) != list(range(nparts)):
        return dict(ok=False, err='missing parts')
    for k in HEAD:
        if any(metas[p][k] != m0[k] for p in metas):
            return dict(ok=False, err=f'inconsistent header field {k}')
    first = 0 if first is None else first
    last = nparts if last is None else last
    dim = len(m0['lo'])
    flo = np.array(m0['lo'], dtype=float); fhi = np.array(m0['hi'], dtype=float); s0 = np.array(m0['split0'])
    lo = [Fr(x) for x in m0['lo']]; hi = [Fr(x) for x in m0['hi']]
    cells = list(np.ndindex(*m0['split0']))
    nleaf = nnode = maxdepth = mismatch = badcell = badside = ncell = 0
    bycode = {253: 0, 254: 0, 255: 0}
    KMAX = 256          # leaf volume = cell volume * 2^-depth; the Kraft sum is kept as an integer multiple of 2^-KMAX
    for p in range(first, last):
        codes = np.load(os.path.join(certdir, f'part{p:04d}.npy'), allow_pickle=False)
        if not side_ok(certdir, p, codes):
            badside += 1
        pos = 0
        for cell in cells[p::nparts]:
            ncell += 1
            fcl = flo + (fhi - flo)*np.array(cell)/s0; fch = flo + (fhi - flo)*(np.array(cell) + 1)/s0
            cl = [lo[k] + (hi[k] - lo[k])*cell[k]/int(s0[k]) for k in range(dim)]
            wd = [(hi[k] - lo[k])/int(s0[k]) for k in range(dim)]
            kraft = 0
            # a box of the tree is cl_k + wd_k [i_k, i_k + 1] / 2^j_k in coordinate k (exact rationals)
            stack = [(fcl, fch, (0,)*dim, (0,)*dim, 0)]
            while stack:
                fl, fh, ii, jj, dep = stack.pop()
                if pos >= len(codes):
                    return dict(ok=False, err=f'part {p}: truncated')
                code = int(codes[pos]); pos += 1; nnode += 1
                maxdepth = max(maxdepth, dep)
                if code in (253, 254, 255):
                    nleaf += 1; bycode[code] += 1
                    if dep > KMAX:
                        return dict(ok=False, err=f'part {p}: depth above {KMAX}')
                    kraft += 1 << (KMAX - dep)
                    c = 0.5*(fl + fh); r = 0.5*(fh - fl)
                    for k in range(dim):
                        step = wd[k]/(1 << jj[k]); l = cl[k] + step*ii[k]
                        fc, fr = Fr(float(c[k])), Fr(float(r[k]))
                        if fc - fr != l or fc + fr != l + step:
                            mismatch += 1
                elif 0 <= code < dim:
                    fmid = 0.5*(fl[code] + fh[code])
                    fl2, fh2 = fl.copy(), fh.copy(); fl2[code] = fmid
                    fl1, fh1 = fl.copy(), fh.copy(); fh1[code] = fmid
                    j2 = jj[:code] + (jj[code] + 1,) + jj[code + 1:]
                    stack.append((fl2, fh2, ii[:code] + (2*ii[code] + 1,) + ii[code + 1:], j2, dep + 1))
                    stack.append((fl1, fh1, ii[:code] + (2*ii[code],) + ii[code + 1:], j2, dep + 1))
                else:
                    return dict(ok=False, err=f'part {p}: invalid code {code}')
            if kraft != 1 << KMAX:
                badcell += 1
        if pos != len(codes):
            return dict(ok=False, err=f'part {p}: trailing data')
    ok = mismatch == 0 and badcell == 0 and badside == 0 and nnode == 2*nleaf - ncell
    return dict(ok=ok, header={k: m0[k] for k in HEAD}, first=first, last=last, cells=ncell, nodes=nnode, leaves=nleaf,
                multi_leaves=bycode[253], fan_leaves=bycode[254], far_leaves=bycode[255], max_depth=maxdepth,
                box_mismatches=mismatch, cell_volume_failures=badcell, side_file_failures=badside)


def combine(paths):
    rs = []
    for path in paths:
        with open(path) as fh:
            rs.append(json.loads(fh.read().strip().splitlines()[-1]))
    if not all('header' in r for r in rs):
        return dict(ok=False, err='a run failed: ' + str([r.get('err') for r in rs if 'header' not in r]))
    h0 = rs[0]['header']
    if any(r['header'] != h0 for r in rs):
        return dict(ok=False, err='runs of different certificates')
    covered = sorted(p for r in rs for p in range(r['first'], r['last']))
    if covered != list(range(h0['nparts'])):
        return dict(ok=False, err='the ranges do not cover every part exactly once')
    tot = {k: sum(r[k] for r in rs) for k in ('cells', 'nodes', 'leaves', 'multi_leaves', 'fan_leaves', 'far_leaves',
                                             'box_mismatches', 'cell_volume_failures', 'side_file_failures')}
    ok = all(r['ok'] for r in rs) and tot['nodes'] == 2*tot['leaves'] - tot['cells']
    return dict(ok=ok, ns=h0['ns'], tau=h0['tau'], parts=h0['nparts'], **tot, max_depth=max(r['max_depth'] for r in rs))


if __name__ == '__main__':
    if sys.argv[1] == '--combine':
        print(json.dumps(combine(sys.argv[2:])), flush=True)
    elif len(sys.argv) == 4:
        print(json.dumps(main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))), flush=True)
    else:
        print(json.dumps(main(sys.argv[1])), flush=True)
