"""v11_run.py LEAVES.npz OUT.jsonl WORKERS [idx-range a:b]: run v11b_leafcheck.check_leaf over the sample in parallel
(one leaf per task, results streamed to OUT.jsonl; leaves already in OUT.jsonl are skipped)."""
import sys, os, json, time
sys.dont_write_bytecode = True
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import v11b_leafcheck as V
from flint import arb
with np.load(sys.argv[1], allow_pickle=False) as _z: lv = {k: _z[k] for k in _z.files}   # arrays in memory before fork
outp = sys.argv[2]; workers = int(sys.argv[3])
tau = arb(str(lv['tau_str']))
n = len(lv['lo'])
if len(sys.argv) > 4:
    a, b = sys.argv[4].split(':'); idxs = list(range(int(a), min(int(b), n)))
else: idxs = list(range(n))
done = set()
if os.path.exists(outp):
    for line in open(outp):
        try: done.add(json.loads(line)['idx'])
        except Exception: pass
idxs = [i for i in idxs if i not in done]

def work(i):
    t0 = time.time(); st = {}
    code = int(lv['code'][i]); ns = int(lv['nstruct'][i]); off = int(lv['soff'][i])
    sh = lv['shifts'][off:off + ns] if ns else None; lm = lv['lam'][off:off + ns] if ns else None
    try:
        ok, v, msg = V.check_leaf(code, list(lv['lo'][i]), list(lv['hi'][i]), tau, sh, lm, 0, st)
    except Exception as e:
        ok, v, msg = False, None, f'EXCEPTION {type(e).__name__}: {e}'
    return dict(idx=i, part=int(lv['part'][i]), pos=int(lv['pos'][i]), code=code, tag=str(lv['tag'][i]), ok=bool(ok),
                minbound=(v.str(15) if v is not None else None), margin=(float((v - tau).lower()) if v is not None else None),
                msg=msg[:300], stats=st, secs=round(time.time() - t0, 2))

if __name__ == '__main__':
    import multiprocessing as mp
    import signal
    with open(outp, 'a') as fo, mp.get_context('fork').Pool(workers) as pool:
        signal.signal(signal.SIGTERM, lambda *a: (pool.terminate(), os._exit(1)))   # kill the parent: workers go too
        for rec in pool.imap_unordered(work, idxs):
            fo.write(json.dumps(rec) + '\n'); fo.flush()
