#!/bin/bash
# usage (from the lean/ directory, after build_l11.sh): bash ../tools/final_l11.sh NPAR
# Compiles the 64 chunk modules blocks/L11/C*.lean and the root module blocks/L11/Root11Good.lean (GoodBox of the
# root box, Hull5Statement, WeakMain5Statement, Main5Statement, MainStatement, WeakMainStatement), then prints the
# axioms of the final theorems (blocks/L11/AxL11.lean).
set -u
NPAR=${1:-40}
LP=$(lake env printenv LEAN_PATH):$PWD/blocks/build
for c in $(seq 0 2047); do [ -f blocks/build/L11/G$c.olean ] || { echo "missing G$c (run build_l11.sh first)"; exit 1; }; done
mkdir -p blocks/logs_final
run() { local n=$1; local s=$(date +%s)
  LEAN_PATH=$LP LEAN_NUM_THREADS=1 lean blocks/L11/$n.lean -o blocks/build/L11/$n.olean > blocks/logs_final/$n.log 2>&1
  echo "$n $? $(( $(date +%s) - s ))" >> blocks/logs_final/done.txt; }
export -f run; export LP
rm -f blocks/logs_final/done.txt
seq 0 63 | sed 's/^/C/' | xargs -P $NPAR -I{} bash -c 'run {}'
grep -v ' 0 ' blocks/logs_final/done.txt && { echo "chunk failures"; exit 1; }
LEAN_PATH=$LP lean blocks/L11/Root11Good.lean -o blocks/build/L11/Root11Good.olean > blocks/logs_final/Root11Good.log 2>&1
echo "Root11Good rc $?"; grep -E "error" blocks/logs_final/Root11Good.log
LEAN_PATH=$LP lean blocks/L11/AxL11.lean 2>&1 | tee blocks/logs_final/axioms.txt | grep -v native_decide
echo "native_decide auxiliaries listed: $(grep -c native_decide blocks/logs_final/axioms.txt)"
