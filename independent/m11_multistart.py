"""Multistart Nelder-Mead for the least hull area of D, B3, B5, B7, B9 (numerical, for the limits section).
Starts: the 8D optimum (opt8_point.json) with B9 placed at random, and random points near the centre of the root box.
Usage: python -I m11_multistart.py NSTART SEED OUT.jsonl"""
import sys, json, math
import numpy as np
from scipy.optimize import minimize
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen11
nst, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
rng = np.random.default_rng(seed)
p8 = [float(x) for x in json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'opt8_point.json')))['params']]
H = np.array([0.19, 0.19, math.pi/5, 0.19, 0.19, 2*math.pi/7, 0.19, 0.19, 2*math.pi/9, 0.19, 0.19])
with open(out, 'a') as fh:
    for k in range(nst):
        if k % 2 == 0:
            x0 = np.array(p8 + [rng.uniform(0, 2*math.pi/9), rng.uniform(-0.03, 0.03), rng.uniform(-0.03, 0.03)])
        else:
            x0 = rng.uniform(-1, 1, 11)*H*np.array([0.15, 0.15, 0, 0.15, 0.15, 0, 0.15, 0.15, 0, 0.15, 0.15])
            x0[[2, 5, 8]] = rng.uniform(0, 1, 3)*H[[2, 5, 8]]
        r = minimize(lambda x: gen11.area(list(x)), x0, method='Nelder-Mead',
                     options={'xatol': 1e-10, 'fatol': 1e-13, 'maxiter': 40000, 'adaptive': True})
        fh.write(json.dumps(dict(seed=seed, start=k, area=float(r.fun), x=[float(v) for v in r.x], nit=int(r.nit))) + '\n'); fh.flush()
