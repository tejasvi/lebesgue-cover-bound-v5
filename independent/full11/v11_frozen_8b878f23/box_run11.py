"""box_run11.py CERTDIR PARTS OUTDIR WORKERS: independent re-check (v11_leafcheck) of EVERY leaf of the listed parts.
Decodes each part with treedec11 (exact boxes, structural checks), checks all leaves in a process pool, and writes per
part: OUTDIR/partNNNN.json (input sha256s, verifier sha256s, counts, fails, minimum margin and its leaf, margin
histogram, CPU seconds) and OUTDIR/partNNNN_margins.npy (float64 margin per leaf in stream order; nan for a fail).
A part's files are written only when all its leaves are done (write to .tmp, then rename)."""
import sys, os, json, time, hashlib, signal
sys.dont_write_bytecode = True
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, 'v11'))
import treedec11, v11_leafcheck as V
from flint import arb
certdir, partsf, outdir, workers = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
parts = [int(x) for x in open(partsf).read().split()]
os.makedirs(outdir, exist_ok=True)
def sha(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()
VER = {f: sha(os.path.join(HERE, 'v11', f)) for f in ('gen11.py', 'v11_leafcheck.py', 'treedec11.py')}
VER['box_run11.py'] = sha(os.path.abspath(__file__))
meta0 = json.load(open(os.path.join(certdir, f'part{parts[0]:04d}.json')))
TAU_STR = repr(float(meta0['tau'])); tau = arb(TAU_STR)
todo = [p for p in parts if not os.path.exists(os.path.join(outdir, f'part{p:04d}.json'))]
LEAVES = {}; SUMM = {}
for p in todo:
    s, leaves = treedec11.decode_part(certdir, p, 'all')
    SUMM[p] = s; LEAVES[p] = leaves
    assert repr(float(s['header']['tau'])) == TAU_STR

def work(task):
    p, k = task
    code, pos, lo, hi, rank, side = LEAVES[p][k]
    t0 = time.process_time(); st = {}
    try:
        if code == 255 or code == 254:
            ok, v, msg = V.check_leaf(254 if code == 254 else 255, lo, hi, tau, None, None, 0, st)
        else:
            ok, v, msg = V.check_leaf(253, lo, hi, tau, np.array(side[0]), np.array(side[1]), 0, st)
    except Exception as e:
        ok, v, msg = False, None, f'EXCEPTION {type(e).__name__}: {e}'
    m = float((v - tau).lower()) if (ok and v is not None) else float('nan')
    return p, k, ok, m, (msg[:300] if not ok else ''), time.process_time() - t0, bool(st.get('split'))

if __name__ == '__main__':
    import multiprocessing as mp
    tasks = [(p, k) for p in todo for k in range(len(LEAVES[p]))]
    left = {p: len(LEAVES[p]) for p in todo}
    marg = {p: np.full(len(LEAVES[p]), np.nan) for p in todo}
    fails = {p: [] for p in todo}; cpu = {p: 0.0 for p in todo}; nsplit = {p: 0 for p in todo}
    t_start = time.time()
    with mp.get_context('fork').Pool(workers) as pool:
        signal.signal(signal.SIGTERM, lambda *a: (pool.terminate(), os._exit(1)))
        for p, k, ok, m, msg, secs, sp in pool.imap_unordered(work, tasks, chunksize=8):
            marg[p][k] = m; cpu[p] += secs; nsplit[p] += sp
            if not ok:
                code, pos, lo, hi, rank, side = LEAVES[p][k]
                fails[p].append(dict(pos=pos, code=code, msg=msg, lo=lo, hi=hi))
            left[p] -= 1
            if left[p] == 0:
                s = SUMM[p]; mm = marg[p]
                okm = mm[np.isfinite(mm)]
                imin = int(np.nanargmin(mm)) if len(okm) else -1
                hist = np.histogram(np.log10(np.maximum(okm, 1e-300)), bins=np.arange(-12, 1.01, 0.5))[0].tolist() if len(okm) else []
                rec = dict(part=p, inputs={f: sha(os.path.join(certdir, f)) for f in (f'part{p:04d}.json', f'part{p:04d}.npy', f'part{p:04d}_multi.npz')
                                            if os.path.exists(os.path.join(certdir, f))},
                           verifier=VER, tau=TAU_STR, decode_errs=s['errs'], counts=s['counts'], leaves=len(mm),
                           checked=int(np.isfinite(mm).sum()), fails=fails[p], nfail=len(fails[p]),
                           min_margin=(float(mm[imin]) if imin >= 0 else None),
                           min_leaf=(dict(pos=LEAVES[p][imin][1], code=LEAVES[p][imin][0]) if imin >= 0 else None),
                           hist_log10_margin=dict(edges=[-12, 1, 0.5], counts=hist), split_leaves=nsplit[p], cpu_s=round(cpu[p], 1))
                np.save(os.path.join(outdir, f'part{p:04d}_margins.tmp.npy'), mm)
                os.replace(os.path.join(outdir, f'part{p:04d}_margins.tmp.npy'), os.path.join(outdir, f'part{p:04d}_margins.npy'))
                with open(os.path.join(outdir, f'part{p:04d}.json.tmp'), 'w') as fo: json.dump(rec, fo)
                os.replace(os.path.join(outdir, f'part{p:04d}.json.tmp'), os.path.join(outdir, f'part{p:04d}.json'))
                del LEAVES[p]
    open(os.path.join(outdir, 'DONE'), 'w').write(f'{len(todo)} parts in {time.time() - t_start:.0f} s\n')
