"""Inner and outer polygon bounds for the hull area at one placement (double precision), with the support function
of lbsearch_v2.py.  Inner: the polygon spanned by the support points of the hull in N equally spaced directions (all of
them lie in the hull).  Outer: the polygon cut out by the N support lines.  Used for the numerical observations of
the section on the limits of the method; not part of any proof.
Usage: python3 area_bracket.py NS P [LOG2N]
  e.g. python3 area_bracket.py 3,5,7 -0.0025482897,-0.0019350278,0.0287183302,0.0250869718,-0.0032906511,0.7016242528,0.0028934171,-0.0127181545 24"""
import sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lbsearch_v2 import Family

ns = [int(v) for v in sys.argv[1].split(',')]
p = np.array([float(v) for v in sys.argv[2].split(',')])
N = 2**int(sys.argv[3]) if len(sys.argv) > 3 else 2**20
fam = Family(ns, N=16)
th = 2*np.pi*np.arange(N)/N
ib, P, H = fam.support(p, th)
x, y = P[:, 0], P[:, 1]
inner = 0.5*np.sum(x*np.roll(y, -1) - np.roll(x, -1)*y)
c, s = np.cos(th), np.sin(th)
c2, s2, H2 = np.roll(c, -1), np.roll(s, -1), np.roll(H, -1)
det = c*s2 - s*c2
vx = (H*s2 - s*H2)/det
vy = (c*H2 - H*c2)/det
outer = 0.5*np.sum(vx*np.roll(vy, -1) - np.roll(vx, -1)*vy)
print(f'N=2^{int(round(np.log2(N)))} inner={inner:.12f} outer={outer:.12f} gap={outer - inner:.2e}')
