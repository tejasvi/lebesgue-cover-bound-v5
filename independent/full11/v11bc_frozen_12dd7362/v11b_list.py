"""v11_list.py LEAVES.npz OUT.jsonl WORKERS idx...: like v11b_run.py for an explicit list of sample indices."""
import sys, os
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.argv = sys.argv[:4] + ['ids:' + ','.join(sys.argv[4:])]
exec(open(os.path.join(HERE, 'v11b_run.py')).read().replace(
    "if len(sys.argv) > 4:\n    a, b = sys.argv[4].split(':'); idxs = list(range(int(a), min(int(b), n)))",
    "if len(sys.argv) > 4 and sys.argv[4].startswith('ids:'):\n    idxs = [int(x) for x in sys.argv[4][4:].split(',')]\nelif len(sys.argv) > 4:\n    a, b = sys.argv[4].split(':'); idxs = list(range(int(a), min(int(b), n)))"))
