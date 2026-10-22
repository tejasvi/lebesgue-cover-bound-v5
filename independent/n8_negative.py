"""Negative tests for the certificate D, B3, B5, B7 (tau = 0.836). Leaf 542149 contains a placement of area 0.83649047
(a numerical optimum), so the checker and the independent verifier must FAIL there for tau = 0.8365, and pass for
tau = 0.836. Root level: a rho7 range ending below 2pi/7, and a t7 range shrunk by 1e-3, must be rejected.
Usage: python -I n8_negative.py CERTDIR LEAVES.npz   (CERTDIR = cert8d_0836; LEAVES.npz from t1_tree.py)"""
import sys, json, os, importlib.util
import numpy as np
from flint import arb
SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'checker', 'lbcheck.py')
spec = importlib.util.spec_from_file_location('lbcheck', SRC); lb = importlib.util.module_from_spec(spec); spec.loader.exec_module(lb)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import v8_leafcheck as V, gen8
lv = np.load(sys.argv[2])
i = 542149
lo, hi = lv['lo'][i], lv['hi'][i]; c = 0.5 * (lo + hi); h = 0.5 * (hi - lo)
p = [-0.0025485, -0.0019337, 0.0287113, 0.0250876, -0.0032904, 0.7016239, 0.0028932, -0.0127181]
print('optimum point inside leaf:', bool(np.all((lo <= p) & (p <= hi))), ' area there', gen8.area(p))
for tau in (0.836, 0.8365):
    ch = lb.Checker([3, 5, 7], tau, 1024, 1e-6)
    ok, msg = ch.check_bound_leaf(c, h)
    print(f'checker, leaf {i}, tau {tau}: ok={ok} {msg}', flush=True)
for tau in ('0.836', '0.8365'):
    ok, msg = V.check_box(list(lo), list(hi), arb(tau), 0, {})
    print(f'independent verifier, leaf {i}, tau {tau}: ok={ok} {msg}', flush=True)
meta = json.load(open(os.path.join(sys.argv[1], 'part0000.json')))
m2 = dict(meta); m2['hi'] = list(meta['hi']); m2['hi'][5] = 0.8975979010256552 - 1e-6
print('root, rho7 range below 2pi/7:', lb.check_root(m2))
m3 = dict(meta); m3['lo'] = list(meta['lo']); m3['hi'] = list(meta['hi']); m3['lo'][6] += 1e-3; m3['hi'][6] -= 1e-3
print('root, t7 range shrunk:', lb.check_root(m3))
print('root, unmodified:', lb.check_root(meta))
