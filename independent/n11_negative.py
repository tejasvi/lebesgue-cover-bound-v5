"""Negative tests of the checker on the 11D certificate: modified copies of the record (symlinks for unchanged files).
Each test directory holds all 2048 headers (presence check) and the files of part TP, one of them modified.
Usage: python -I n11_negative.py CERTDIR OUTDIR    (then run checker/lbcheck.py OUTDIR/T* 1618)"""
import sys, os, json, shutil
import numpy as np
SRC = sys.argv[1]
OUT = sys.argv[2]; TP = 1618
os.makedirs(OUT)
def base(name):
    d = os.path.join(OUT, name); os.makedirs(d)
    for f in os.listdir(SRC):
        if f.startswith('part') and (f.endswith('.json') or f.startswith(f'part{TP:04d}')):
            os.symlink(os.path.join(SRC, f), os.path.join(d, f))
    return d
def replace(d, f, writer):
    p = os.path.join(d, f); os.remove(p); writer(p)
# T1: tau raised to 0.8371 in every header
d = base('T1_tau'); 
for f in sorted(os.listdir(d)):
    if f.endswith('.json'):
        m = json.load(open(os.path.join(SRC, f))); m['tau'] = 0.8371
        replace(d, f, lambda p, m=m: json.dump(m, open(p, 'w')))
# T2: range of rho_4 shortened to [0, 0.69] in every header
d = base('T2_root')
for f in sorted(os.listdir(d)):
    if f.endswith('.json'):
        m = json.load(open(os.path.join(SRC, f))); m['hi'][8] = 0.69
        replace(d, f, lambda p, m=m: json.dump(m, open(p, 'w')))
codes = np.load(os.path.join(SRC, f'part{TP:04d}.npy'))
z = dict(np.load(os.path.join(SRC, f'part{TP:04d}_multi.npz')))
# T3: first split of the tree turned into a fan leaf
d = base('T3_tree'); c2 = codes.copy(); assert c2[0] < 11; c2[0] = 254
replace(d, f'part{TP:04d}.npy', lambda p: np.save(p, c2))
# T4: one weight of the first combination leaf made negative
d = base('T4_negw'); z4 = {k: v.copy() for k, v in z.items()}; z4['lam'][0] = -1e-8
replace(d, f'part{TP:04d}_multi.npz', lambda p: np.savez(p, **z4))
# T5: entry of the first combination leaf removed from the side file
d = base('T5_missing'); n0 = int(z['nstruct'][0])
z5 = dict(pos=z['pos'][1:], nstruct=z['nstruct'][1:], shifts=z['shifts'][n0:], lam=z['lam'][n0:])
replace(d, f'part{TP:04d}_multi.npz', lambda p: np.savez(p, **z5))
# T6: extra side-file entry for a fan leaf (code 254)
d = base('T6_extra'); j = int(np.nonzero(codes == 254)[0][0])
z6 = dict(pos=np.concatenate([z['pos'], [j]]), nstruct=np.concatenate([z['nstruct'], [1]]),
          shifts=np.concatenate([z['shifts'], np.zeros((1, 11), np.int8)]), lam=np.concatenate([z['lam'], [1.0]]))
replace(d, f'part{TP:04d}_multi.npz', lambda p: np.savez(p, **z6))
# T7: all weights of the first combination leaf set to 0
d = base('T7_zerow'); z7 = {k: v.copy() for k, v in z.items()}; z7['lam'][:n0] = 0.0
replace(d, f'part{TP:04d}_multi.npz', lambda p: np.savez(p, **z7))
print('made', sorted(os.listdir(OUT)))
