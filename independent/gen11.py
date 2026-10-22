"""gen8 geometry (exact hull area via the support function, inner/outer polygon bounds) for D, B3, B5, B7, B9 in the
parameter layout of the 11D certificate: p = [t1x, t1y, rho2, t2x, t2y, rho3, t3x, t3y, rho4, t4x, t4y].
Only placements() differs from gen8, which is imported from gen8.py in this directory."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen8
NS = (3, 5, 7, 9)


def placements(p):
    out = [(NS[0], 0.0, (p[0], p[1]))]
    for i, n in enumerate(NS[1:]):
        out.append((n, p[2 + 3*i], (p[3 + 3*i], p[4 + 3*i])))
    return out


gen8.placements = placements
area = gen8.area
poly_bounds = gen8.poly_bounds
