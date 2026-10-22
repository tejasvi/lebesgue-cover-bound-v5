#!/usr/bin/env python3
"""Polish five-body (D, B3, B5, B7, B9) hull-area local minima from given starts: repeated Nelder-Mead restarts with
shrinking simplices, then Powell, on gen11.area (exact support-function area).
  p11_polish.py STARTS.json I0 I1 OUT.jsonl     (starts[i] = {"area": a, "x": [11 floats], "src": ...})"""
import sys, os, json
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen11
starts = json.load(open(sys.argv[1])); i0, i1, out = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
fun = lambda x: gen11.area(list(x))
with open(out, 'a') as fh:
    for r in starts[i0:i1]:
        x = np.array(r['x'], float); fx = fun(x)
        for it in range(30):
            scale = 1e-3 * 0.5 ** it
            sim = np.vstack([x] + [x + scale * np.eye(11)[k] for k in range(11)])
            y = minimize(fun, x, method='Nelder-Mead', options={'initial_simplex': sim, 'xatol': 1e-12, 'fatol': 1e-15, 'maxfev': 6000, 'adaptive': True})
            z = minimize(fun, y.x, method='Powell', options={'xtol': 1e-12, 'ftol': 1e-15, 'maxfev': 4000})
            cand = min((y.fun, list(y.x)), (z.fun, list(z.x)))
            if cand[0] < fx - 1e-14:
                x, fx = np.array(cand[1]), cand[0]
            elif it > 2:
                break
        fh.write(json.dumps(dict(src=r.get('src'), start_area=r['area'], area=float(fx), x=[float(v) for v in x])) + '\n'); fh.flush()
