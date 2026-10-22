"""Counts for the final 11D certificate in blocks/L11: modules, leaves (single-fan L / combination C), nodes, native axioms."""
import os, re, glob, json, sys
d = sys.argv[1] if len(sys.argv) > 1 else 'blocks/L11'
cnt = dict(B=0, S=0, G=0, C=0, single=0, comb=0, nodes=0, delegated=0)
rx = re.compile(r'def codes : String := "([^"]*)"')
for f in glob.glob(os.path.join(d, '*.lean')):
    b = os.path.basename(f)
    k = b[0]
    if k in 'BSGC' and b[1].isdigit(): cnt[k] += 1
    if k in 'BS':
        m = rx.search(open(f).read())
        if m:
            s = m.group(1); cnt['single'] += s.count('L'); cnt['comb'] += s.count('C')
            cnt['delegated'] += s.count('X'); cnt['nodes'] += len(s)
cnt['leaves'] = cnt['single'] + cnt['comb']
cnt['nodes_without_delegation_markers'] = cnt['nodes'] - cnt['delegated']
print(json.dumps(cnt))
