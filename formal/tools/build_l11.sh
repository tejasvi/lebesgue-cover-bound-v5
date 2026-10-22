#!/bin/bash
# usage (from the lean/ directory, after `lake build` and after unpacking l11_sources.tar.zst into blocks/):
#   bash ../tools/build_l11.sh NPAR
# Compiles the generated certificate modules blocks/L11/{S*,B*}.lean with native_decide (the compiled checker
# libraries of LebFast are loaded with --load-dynlib), then the glue modules blocks/L11/G*.lean.
# Output: blocks/build/L11/*.olean; log: blocks/logs/done.txt (module, exit code, seconds).
set -u
NPAR=${1:-$(nproc)}
D=.lake/build/lib/lean
LP=$(lake env printenv LEAN_PATH):$PWD/blocks/build
mkdir -p blocks/build/L11 blocks/logs
DL=""; for m in Heur Model Exact Driver Tree VT Root11; do DL="$DL --load-dynlib=$D/LebesgueCover_LebFast_$m.so"; done
run() {
  local n=$1; local s=$(date +%s.%N)
  [ -f blocks/build/L11/$n.olean ] && { echo "$n 0 skip" >> blocks/logs/done.txt; return; }
  LEAN_PATH=$LP LEAN_NUM_THREADS=1 lean $2 blocks/L11/$n.lean -o blocks/build/L11/$n.olean > blocks/logs/$n.log 2>&1
  local r=$?; echo "$n $r $(awk "BEGIN{print $(date +%s.%N) - $s}")" >> blocks/logs/done.txt
}
export -f run; export LP DL
ls -S blocks/L11/ | grep '^S.*\.lean$' | sed 's/\.lean$//' | xargs -P $NPAR -I{} bash -c 'run {} "$DL"'
ls -S blocks/L11/ | grep '^B.*\.lean$' | sed 's/\.lean$//' | xargs -P $NPAR -I{} bash -c 'run {} "$DL"'
MEMG=$(free -g | awk '/Mem:/{print $2}'); GPAR=$((MEMG/4)); [ $GPAR -gt $((NPAR/4+1)) ] && GPAR=$((NPAR/4+1)); [ $GPAR -lt 1 ] && GPAR=1
ls blocks/L11/ | grep '^G.*\.lean$' | sed 's/\.lean$//' | xargs -P $GPAR -I{} bash -c 'run {} ""'
echo "ok $(grep -c ' 0 ' blocks/logs/done.txt) fail $(grep -vc ' 0 ' blocks/logs/done.txt)"
