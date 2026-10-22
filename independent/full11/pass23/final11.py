"""final11.py: accounting of the full independent re-check of cert11d_08366 (all leaves).
Pass 1 (v11_frozen_8b878f23, fleet11/results): every part 0..2047 exactly once, input sha256s equal to the record's
SHA256SUMS, verifier sha256s equal to the frozen copy, no decode errors, counts equal to the independent decode, every
leaf checked.  A leaf that pass 1 did not verify must be verified by a later pass: pass 2 (v11b) or pass 3 (v11c) of
v11bc_frozen_12dd7362, or pass 3d (v11c fixed) of v11d_frozen_888b6867, read from pass23/results/*.jsonl with the
code sha256s in the .meta files and the leaves identified through the fails_*.npz files (decoded by treedec11).
Prints the counts per pass, the smallest margins, and the verdict."""
import sys, os, json, hashlib
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); A11 = os.path.dirname(HERE)
CERT = os.path.join(A11, '..', 'cert11d_08366'); RES = os.path.join(A11, 'fleet11', 'results')
F1 = os.path.join(A11, 'v11_frozen_8b878f23'); FBC = os.path.join(A11, 'v11bc_frozen_12dd7362'); FD = os.path.join(A11, 'v11d_frozen_888b6867')
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
sums = {}
for line in open(os.path.join(CERT, 'SHA256SUMS')):
    h, f = line.split(None, 1); sums[f.strip().lstrip('*').split('/')[-1]] = h
ver1 = {f: sha(os.path.join(F1, f)) for f in ('gen11.py', 'v11_leafcheck.py', 'treedec11.py', 'box_run11.py')}
counts = {p['part']: p['counts'] for p in json.load(open(os.path.join(A11, 'treedec11_all.json')))['parts']}
problems = []; got = {}
for box in sorted(os.listdir(RES)):
    for f in sorted(os.listdir(os.path.join(RES, box))):
        if f.startswith('part') and f.endswith('.json'):
            r = json.load(open(os.path.join(RES, box, f)))
            if r['part'] not in got: got[r['part']] = (r, box)
fails1 = {}; n1 = 0; min1 = []; cpu = 0.0; split1 = 0
for p in range(2048):
    if p not in got: problems.append(f'part {p}: no pass-1 result'); continue
    r, box = got[p]
    for f, h in r['inputs'].items():
        if sums.get(f) != h: problems.append(f'part {p}: input {f} differs from SHA256SUMS')
    need = {f'part{p:04d}.json', f'part{p:04d}.npy'} | ({f'part{p:04d}_multi.npz'} if counts[p]['253'] else set())
    if not need <= set(r['inputs']): problems.append(f'part {p}: inputs missing')
    if r['verifier'] != ver1: problems.append(f'part {p}: pass-1 verifier differs from the frozen copy')
    if r['decode_errs']: problems.append(f'part {p}: decode errors')
    if r['counts'] != counts[p]: problems.append(f'part {p}: counts differ from the decode')
    n = sum(counts[p].values())
    if r['leaves'] != n: problems.append(f'part {p}: leaves {r["leaves"]} of {n}')
    m = np.load(os.path.join(RES, box, f'part{p:04d}_margins.npy'))
    if len(m) != n: problems.append(f'part {p}: margins file length')
    if int(np.isnan(m).sum()) != r['nfail']: problems.append(f'part {p}: fail count and margins disagree')
    for x in r['fails']: fails1[(p, x['pos'])] = x['code']
    n1 += n - r['nfail']; cpu += r['cpu_s']; split1 += r['split_leaves']
    if r['min_margin'] is not None: min1.append((r['min_margin'], p, r['min_leaf']))
min1.sort()
# later passes
passes = [('2 (v11b)', 'pass2_a', 'fails_a.npz', FBC), ('3 (v11c)', 'pass3_a', 'fails_a.npz', FBC),
          ('3d (v11c fixed)', 'pass3d_a', 'fails_a.npz', FD), ('3d (v11c fixed)', 'pass3d_b', 'fails_b.npz', FD)]
extra = sorted(f[:-6] for f in os.listdir(os.path.join(HERE, 'results')) if f.startswith('pass3d_c') and f.endswith('.jsonl'))
for e in extra: passes.append(('3d (v11c fixed)', e, e.replace('pass3d_', 'fails_') + '.npz', FD))
resolved = {}; per = {}; minlater = []
for label, stem, npz, fdir in passes:
    jl = os.path.join(HERE, 'results', stem + '.jsonl')
    if not os.path.exists(jl): problems.append(f'missing {stem}.jsonl'); continue
    meta = json.load(open(jl + '.meta'))
    want = {f: sha(os.path.join(fdir, f)) for f in meta if os.path.exists(os.path.join(fdir, f))}
    if any(meta[f] != want.get(f) for f in ('v11b_leafcheck.py', 'v11c_leafcheck.py', 'gen11.py', 'treedec11.py')):
        problems.append(f'{stem}: code sha256s differ from {os.path.basename(fdir)}')
    with np.load(os.path.join(HERE, npz), allow_pickle=False) as z:
        part, pos, code = z['part'], z['pos'], z['code']
    for line in open(jl):
        r = json.loads(line)
        i = r['idx']; key = (int(part[i]), int(pos[i]))
        if (r['part'], r['pos']) != key: problems.append(f'{stem}: idx {i} does not match its npz entry'); continue
        if r['ok'] and key in fails1 and key not in resolved:
            resolved[key] = label; per[label] = per.get(label, 0) + 1
            minlater.append((r['margin'], key[0], key[1], label))
unres = [k for k in fails1 if k not in resolved]
if unres: problems.append(f'{len(unres)} pass-1 fails not resolved by a later pass, e.g. {unres[:5]}')
minlater.sort()
total = sum(sum(c.values()) for c in counts.values())
summary = dict(leaves=total, pass1_verified=n1, pass1_fails=len(fails1), later=per, unresolved=len(unres),
               pass1_cpu_hours=round(cpu / 3600, 1), pass1_split_leaves=split1, pass1_smallest_margins=min1[:5],
               later_smallest_margins=minlater[:5], problems=problems[:30], n_problems=len(problems),
               verdict=('ALL %d LEAVES VERIFIED' % total if not problems and n1 + len(resolved) == total else 'NOT VERIFIED'))
json.dump(summary, open(os.path.join(HERE, 'FINAL11.json'), 'w'), indent=1)
print(json.dumps(summary, indent=1))
