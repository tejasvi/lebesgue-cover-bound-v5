"""Export of the 11D certificate: one block per grid cell (B = 1), delegated subtrees for big cells.
usage: mkblocks3.py OUTDIR(search cells) LEANDIR T CELLS...   (CELLS = comma list of cell indices present in OUTDIR)
Writes LEANDIR/L11/{B<ci>,S<ci>_<k>,G<ci>}.lean using LebFast.Root11 (ns11, tau11, rl11, rh11) and LebFast.VT (VQ)."""
import sys, os, json
from fractions import Fraction as Fr
import numpy as np
outdir, leandir, T = sys.argv[1], sys.argv[2], int(sys.argv[3])
summ = json.load(open(os.path.join(outdir, 'summary.json'))); hd = summ['header']
cells = sorted(int(c) for c in summ['cells']) if sys.argv[4] == 'auto' else [int(c) for c in sys.argv[4].split(',')]
lo0 = [Fr(x) for x in hd['lo']]; hi0 = [Fr(x) for x in hd['hi']]; s0 = hd['split0']; d = len(lo0)
# the search's root box must be the Lean root box (LebFast/Root11.lean) exactly
import re
r11 = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean', 'LebFast', 'Root11.lean')).read()
def arr(name):
    body = re.search(r'def ' + name + r' : Array Rat := #\[(.*?)\]', r11).group(1)
    return [Fr(int(a), int(b)) for a, b in re.findall(r'mkRat \((-?\d+)\) (\d+)', body)]
assert arr('rl11') == lo0 and arr('rh11') == hi0, 'root box differs from LebFast/Root11.lean'
assert Fr(repr(float(hd['tau']))) == Fr(4183, 5000) and hd['ns'] == [3, 5, 7, 9]
e = s0[0].bit_length() - 1
def grid(lo, hi, splits):
    if not splits: return [(lo, hi)]
    a = splits[0]; m = (lo[a] + hi[a])/2
    l2 = list(hi); l2[a] = m; r2 = list(lo); r2[a] = m
    return grid(lo, l2, splits[1:]) + grid(r2, hi, splits[1:])
allcells = grid(lo0, hi0, [a for a in range(d) for _ in range(e)])
def ch(c):
    if c == 254: return 'L'
    if c == 252: return 'C'
    if c == 250: return 'X'
    return str(c) if c < 10 else chr(ord('a') + c - 10)
def q(x): x = Fr(x); return f'{x.numerator}/{x.denominator}' if x.denominator != 1 else f'{x.numerator}'
def boxstr(b): return ' '.join(q(x) for x in b)
def sidestr(entries):
    return '|'.join(';'.join(('a' if N == 256 else 'b') + ''.join('-' if v < 0 else ('+' if v > 0 else '0') for v in sv) + ':' + str(int(round(lam*2**40))) for sv, lam, N in fans) for fans in entries)
def parse(codes, side, lo, hi):
    pos = [0]; sp = [0]
    def rec(lo, hi):
        c = codes[pos[0]]; pos[0] += 1
        if c >= 250:
            sd = []
            if c == 252: sd = [side[sp[0]]]; sp[0] += 1
            return dict(c=c, lo=lo, hi=hi, kids=None, leaves=1, side=sd)
        m = (lo[c] + hi[c])/2
        l2 = list(hi); l2[c] = m; r2 = list(lo); r2[c] = m
        k1 = rec(lo, l2); k2 = rec(r2, hi)
        return dict(c=c, lo=lo, hi=hi, kids=(k1, k2), leaves=k1['leaves'] + k2['leaves'], side=k1['side'] + k2['side'])
    r = rec(lo, hi); assert pos[0] == len(codes) and sp[0] == len(side)
    return r
def flat(node):
    if node['kids'] is None: return ch(node['c'])
    return ch(node['c']) + flat(node['kids'][0]) + flat(node['kids'][1])
def skeleton(node, subs):
    if node['kids'] is None: return ch(node['c']), node['side']
    if node['leaves'] <= T: subs.append(node); return 'X', []
    s1, d1 = skeleton(node['kids'][0], subs); s2, d2 = skeleton(node['kids'][1], subs)
    return ch(node['c']) + s1 + s2, d1 + d2
od = os.path.join(leandir, 'L11'); os.makedirs(od, exist_ok=True)
CK = 'checkCellStr ns11 VQ (mkRat 1 (2 ^ 36)) tau11'
man = []
for ci in cells:
    codes = np.load(os.path.join(outdir, f'cell{ci:04d}.npy')).tolist()
    side = json.load(open(os.path.join(outdir, f'cell{ci:04d}_side.json')))
    root = parse(codes, side, allcells[ci][0], allcells[ci][1])
    subs = []
    if root['leaves'] <= T: skel, sd = flat(root), root['side']
    else: skel, sd = skeleton(root, subs)
    names = []
    for k, node in enumerate(subs):
        nm = f'S{ci}_{k}'
        open(os.path.join(od, nm + '.lean'), 'w').write('\n'.join([
            'import LebFast.Tree', 'import LebFast.VT', 'import LebFast.Root11', 'open LebesgueCover.Fast', f'namespace L11.{nm}',
            f'def lo : String := "{boxstr(node["lo"])}"', f'def hi : String := "{boxstr(node["hi"])}"',
            f'def codes : String := "{flat(node)}"', f'def side : String := "{sidestr(node["side"])}"',
            f'theorem ok : {CK} lo hi codes side = true := by native_decide', f'end L11.{nm}']) + '\n')
        names.append(nm)
    subl = '[' + ', '.join(f'(L11.{nm}.lo, L11.{nm}.hi)' for nm in names) + ']'
    open(os.path.join(od, f'B{ci}.lean'), 'w').write('\n'.join(
        ['import LebFast.Tree', 'import LebFast.VT', 'import LebFast.Root11'] + [f'import L11.{nm}' for nm in names] +
        ['open LebesgueCover.Fast', f'namespace L11.B{ci}', f'def codes : String := "{skel}"', f'def side : String := "{sidestr(sd)}"',
         f'def subs : List (String × String) := {subl}',
         f'theorem ok : checkBlockStr ns11 VQ (mkRat 1 (2 ^ 36)) tau11 rl11 rh11 11 1 {ci} 1 codes side subs = true := by native_decide',
         f'end L11.B{ci}']) + '\n')
    if names:
        hs = '(by simp only [L11.B' + str(ci) + '.subs, List.forall_mem_cons]; exact ⟨' + ', '.join(f'checkCellStr_good hV L11.{nm}.ok' for nm in names) + ', fun _ h => by simp at h⟩)'
    else:
        hs = f'(fun p hp => by simp [L11.B{ci}.subs] at hp)'
    open(os.path.join(od, f'G{ci}.lean'), 'w').write('\n'.join([
        'import LebesgueCover.TreeSound', f'import L11.B{ci}', 'open LebesgueCover.Cert LebesgueCover.Fast', f'namespace L11.G{ci}',
        'set_option maxRecDepth 100000 in',
        'theorem good (hV : VertTableOK ns11 VQ (mkRat 1 (2 ^ 36))) :',
        f'    ∀ c ∈ ((gridCells (gridSplits 11 1) rl11 rh11).drop ({ci} * 1)).take 1,',
        '      GoodBox ns11 tau11 (fun i => c.1.getD i 0) (fun i => c.2.getD i 0) :=',
        f'  block_good hV {hs} L11.B{ci}.ok', f'end L11.G{ci}']) + '\n')
    man.append(dict(cell=ci, leaves=root['leaves'], subs=len(names), skel_leaves=skel.count('L') + skel.count('C')))
json.dump(man, open(os.path.join(od, f'manifest_{cells[0]}.json'), 'w'))
print('cells', len(cells), 'leaves', sum(m['leaves'] for m in man), 'subs', sum(m['subs'] for m in man))
