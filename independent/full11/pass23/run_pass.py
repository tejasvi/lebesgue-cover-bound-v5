"""run_pass.py PASS CODEDIR LEAVES.npz OUT.jsonl WORKERS [IDXFILE]: run pass 2 (v11b check_leaf) or pass 3 (v11c
check_leaf_c, own Lemma K) of the 11D re-check on the leaves of LEAVES.npz (or the indices listed in IDXFILE), in a
process pool; one JSON line per leaf (streamed), leaves already in OUT.jsonl are skipped.  CODEDIR is the frozen
v11bc directory; its file sha256s are written to OUT.jsonl.meta."""
import sys, os, json, time, hashlib, signal
sys.dont_write_bytecode = True
import numpy as np
pas, codedir, leaves, outp, workers = sys.argv[1], os.path.abspath(sys.argv[2]), sys.argv[3], sys.argv[4], int(sys.argv[5])
sys.path.insert(0, codedir)
import v11b_leafcheck as B, v11c_leafcheck as Cc
from flint import arb
with np.load(leaves, allow_pickle=False) as z: lv = {k: z[k] for k in z.files}
tau = arb(str(lv['tau_str']))
idxs = [int(x) for x in open(sys.argv[6]).read().split()] if len(sys.argv) > 6 else list(range(len(lv['lo'])))
done = set()
if os.path.exists(outp):
    for line in open(outp):
        try: done.add(json.loads(line)['idx'])
        except Exception: pass
idxs = [i for i in idxs if i not in done]
json.dump({f: hashlib.sha256(open(os.path.join(codedir, f), 'rb').read()).hexdigest() for f in sorted(os.listdir(codedir)) if f.endswith('.py')},
          open(outp + '.meta', 'w'))

def work(i):
    t0 = time.time(); st = {}
    code = int(lv['code'][i]); ns = int(lv['nstruct'][i]); off = int(lv['soff'][i])
    sh = lv['shifts'][off:off + ns] if ns else None; lm = lv['lam'][off:off + ns] if ns else None
    try:
        if pas == '2':
            ok, v, msg = B.check_leaf(code, list(lv['lo'][i]), list(lv['hi'][i]), tau, sh, lm, 0, st)
        else:
            ok, v, msg = Cc.check_leaf_c(list(lv['lo'][i]), list(lv['hi'][i]), tau, sh, 0, st)
    except Exception as e:
        ok, v, msg = False, None, f'EXCEPTION {type(e).__name__}: {e}'
    return dict(idx=i, part=int(lv['part'][i]), pos=int(lv['pos'][i]), code=code, ok=bool(ok), pass_=pas,
                minbound=(v.str(15) if v is not None else None), margin=(float((v - tau).lower()) if v is not None else None),
                msg=msg[:300], stats={k: (v2 if not isinstance(v2, list) else v2[:8]) for k, v2 in st.items()}, secs=round(time.time() - t0, 2))

if __name__ == '__main__':
    import multiprocessing as mp
    with open(outp, 'a') as fo, mp.get_context('fork').Pool(workers) as pool:
        signal.signal(signal.SIGTERM, lambda *a: (pool.terminate(), os._exit(1)))
        for rec in pool.imap_unordered(work, idxs):
            fo.write(json.dumps(rec) + '\n'); fo.flush()
