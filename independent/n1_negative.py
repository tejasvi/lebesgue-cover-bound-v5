"""Negative tests of the checker ../checker/lbcheck.py (imported from its path, not modified), certificate D, B3, B5.
(1) leaf level: the leaf containing Mishra's optimum must FAIL for tau = 0.8348 (true minimum there 0.83478095 < tau);
(2) root level: a translation box shrunk by 1e-3 and a rotation range ending below pi/5 must be rejected;
(3) tree level (on copies in WORKDIR): a split code turned into a leaf code, a dropped last code,
    a missing part, an inconsistent header.
Usage: python -I n1_negative.py CERTDIR LEAVES.npz WORKDIR   (LEAVES.npz from t1_tree.py; WORKDIR is replaced)
"""
import sys, os, json, shutil, importlib.util
import numpy as np
from flint import arb

SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'checker', 'lbcheck.py')
CERT = sys.argv[1]
NEG = sys.argv[3]
spec = importlib.util.spec_from_file_location('lbcheck', SRC); lb = importlib.util.module_from_spec(spec); spec.loader.exec_module(lb)
lv = np.load(sys.argv[2])

# (1)
for i in (18433, 11758):
    c = 0.5 * (lv['lo'][i] + lv['hi'][i]); h = 0.5 * (lv['hi'][i] - lv['lo'][i])
    for tau in (0.8347, 0.83478, 0.8348):
        ch = lb.Checker([3, 5], tau, 1024, 1e-6)
        ok, msg = ch.check_bound_leaf(c, h)
        print(f'(1) leaf {i} tau {tau}: ok={ok} {msg}', flush=True)

# (2)
meta = json.load(open(os.path.join(CERT, 'part0000.json')))
m2 = dict(meta); m2['lo'] = list(meta['lo']); m2['hi'] = list(meta['hi'])
m2['lo'][0] += 1e-3; m2['hi'][0] -= 1e-3
print('(2a) shrunk t3 range:', lb.check_root(m2))
m3 = dict(meta); m3['hi'] = list(meta['hi']); m3['hi'][2] = 0.6283185307179586 - 1e-6
print('(2b) rho range below pi/5:', lb.check_root(m3))
m4 = dict(meta); m4['tau'] = 0.8348
print('(2c) header tau 0.8348 with the same root box:', lb.check_root(m4))
print('(2d) unmodified root:', lb.check_root(meta))

# (3)
if os.path.exists(NEG): shutil.rmtree(NEG)
def fresh(name):
    d = os.path.join(NEG, name); shutil.copytree(CERT, d, copy_function=shutil.copyfile)
    for f in os.listdir(d):
        if not (f.startswith('part') and (f.endswith('.json') or f.endswith('.npy'))): os.remove(os.path.join(d, f))
    return d
d = fresh('split_to_leaf'); codes = np.load(os.path.join(d, 'part0010.npy'))
k = int(np.nonzero(codes < 5)[0][0]); codes[k] = 254; np.save(os.path.join(d, 'part0010.npy'), codes)
print('(3a) part 10, first split code -> leaf:', json.dumps(lb.check_part(d, 10)), flush=True)
d = fresh('drop_last'); codes = np.load(os.path.join(d, 'part0006.npy')); np.save(os.path.join(d, 'part0006.npy'), codes[:-1])
print('(3b) part 6, last code dropped:', json.dumps(lb.check_part(d, 6)), flush=True)
d = fresh('missing_part'); os.remove(os.path.join(d, 'part0007.json')); os.remove(os.path.join(d, 'part0007.npy'))
print('(3c) part 7 removed, present check:', lb.check_all_present(d))
d = fresh('bad_header'); m = json.load(open(os.path.join(d, 'part0003.json'))); m['split0'] = [4, 4, 4, 4, 2]
json.dump(m, open(os.path.join(d, 'part0003.json'), 'w'))
print('(3d) part 3 header split0 changed, present check:', lb.check_all_present(d))
d = fresh('leaf_to_split'); codes = np.load(os.path.join(d, 'part0000.npy')); codes[0] = 0; np.save(os.path.join(d, 'part0000.npy'), codes)
print('(3e) part 0, first leaf code -> split:', json.dumps(lb.check_part(d, 0)), flush=True)
