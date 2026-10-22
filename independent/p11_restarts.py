#!/usr/bin/env python3
"""Perturbation restarts around a five-body local minimum (kinked: Nelder-Mead stalls): x = best + s * N(0, 1) with
s from 1e-3 down to 1e-6, polish (adaptive Nelder-Mead with a small simplex, then Powell), keep improvements.
  p11_restarts.py X.json SEED NREST OUT.jsonl    (X.json = {"x": [11 floats]})"""
import sys, os, json
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen11
x = np.array(json.load(open(sys.argv[1]))['x'], float); seed, nrest, out = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = np.random.default_rng(seed)
fun = lambda v: gen11.area(list(v))
fx = fun(x); scales = [1e-3, 3e-4, 1e-4, 3e-5, 1e-5, 3e-6, 1e-6]
for it in range(nrest):
    s = scales[it % len(scales)]
    x0 = x + s * rng.standard_normal(11)
    sim = np.vstack([x0] + [x0 + s * np.eye(11)[k] for k in range(11)])
    y = minimize(fun, x0, method='Nelder-Mead', options={'initial_simplex': sim, 'xatol': 1e-13, 'fatol': 1e-16, 'maxfev': 5000, 'adaptive': True})
    z = minimize(fun, y.x, method='Powell', options={'xtol': 1e-13, 'ftol': 1e-16, 'maxfev': 3000})
    v, xv = min((y.fun, list(y.x)), (z.fun, list(z.x)))
    if v < fx - 1e-15:
        x, fx = np.array(xv), v
with open(out, 'w') as fh:
    fh.write(json.dumps(dict(seed=seed, area=float(fx), x=[float(t) for t in x])) + '\n')
