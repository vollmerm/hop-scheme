#!/usr/bin/env bash
# Compiles each bench program under a list of configurations and prints static
# and dynamic metrics, after checking the result against the host Scheme.
#   tools/bench-run.sh [FILE...]        (default: bench/*.scm)
# Configurations (BENCH_CONFIGS overrides, space separated):
#   off              no SSA, nothing else
#   prune            only drop unread top-level definitions and dead procedures
#   control          SSA round trip, analysis off
#   k0 k1 k2 k3 k8   HOP_SSA=sccp at depth k
#   pK               k with pruning;  iK  k with pruning and inlining
#   jK               pruning and interprocedural summaries (HOP_IPA);  aK  also inlining
#   ioff             pruning and inlining, no SSA
# HOP_INLINE_SIZE (default 30) is the inlining size limit.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export HOP_CHECK_ALLOC=1
HEAP="${HOP_HEAP_BYTES:-67108864}"
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
files=("$@"); [[ ${#files[@]} -eq 0 ]] && files=("$ROOT"/bench/*.scm)

# Each program's last expression is wrapped in a loop of BENCH_REPEAT iterations
# (summing the results) so that the run is long enough to measure; BENCH_REPEAT=1
# keeps the program as it is.
REPEAT="${BENCH_REPEAT:-2000}"
scale_program() {
  csi -R r7rs -I "$ROOT" -e "
    (import (scheme base) (scheme file) (scheme read) (scheme write))
    (define forms (call-with-input-file \"$1\"
      (lambda (p) (let loop ((acc '())) (let ((f (read p))) (if (eof-object? f) (reverse acc) (loop (cons f acc))))))))
    (define last-form (car (reverse forms)))
    (call-with-output-file \"$2\"
      (lambda (out)
        (for-each (lambda (f) (write f out) (newline out)) (reverse (cdr (reverse forms))))
        (write (if (= $REPEAT 1) last-form
                   '(letrec ((bench-rep (lambda (bench-i bench-acc)
                                          (if (= bench-i $REPEAT) bench-acc
                                              (bench-rep (+ bench-i 1) (+ bench-acc LAST))))))
                      (bench-rep 0 0))) out)
        (newline out)))" >/dev/null
  if (( REPEAT != 1 )); then
    # splice the original last form in place of LAST
    python3 - "$1" "$2" <<'PY'
import sys,re
src=open(sys.argv[1]).read()
out=open(sys.argv[2]).read()
# the original last top-level form is the final balanced expression of src
depth=0; start=None; last=None
i=0
while i < len(src):
    c=src[i]
    if c==';':
        while i < len(src) and src[i]!='\n': i+=1
        continue
    if c=='(':
        if depth==0: start=i
        depth+=1
    elif c==')':
        depth-=1
        if depth==0: last=src[start:i+1]
    i+=1
open(sys.argv[2],'w').write(out.replace('LAST',last))
PY
  fi
}

# Process startup costs the same for every program: measure it once on an empty
# program and report instructions retired above it.
echo '(+ 1 2)' > "$WORK/empty.scm"
csi -R r7rs -I "$ROOT" -e "(begin (load \"$ROOT/compiler.scm\") (write-aarch64-program-file \"$WORK/empty.scm\" \"$WORK/empty.s\"))"
clang -arch arm64 -o "$WORK/empty" "$WORK/empty.s" "$ROOT/runtime.c" "$ROOT/codegen_harness.c"
BASE=$(/usr/bin/time -l "$WORK/empty" 2>&1 >/dev/null | awk '/instructions retired/ {print $1}')

printf '%-10s %-8s %6s %5s %5s %6s %12s %12s\n' program config lines car cdr alloc work-instrs dyn-allocs
for f in "${files[@]}"; do
  name="$(basename "$f" .scm)"
  scaled="$WORK/$name.scm"
  scale_program "$f" "$scaled"
  expected="$(csi -R r7rs -I "$ROOT" -s "$ROOT/tools/host-eval.scm" "$scaled")"
  for config in ${BENCH_CONFIGS:-off prune ioff i0 i1 i2 i3 i8}; do
    case "$config" in
      off) envs=(HOP_SSA=) ;;
      prune) envs=(HOP_SSA= HOP_PRUNE=1) ;;
      control) envs=(HOP_SSA=control) ;;
      ioff) envs=(HOP_SSA= HOP_PRUNE=1 "HOP_INLINE=${HOP_INLINE_SIZE:-30}") ;;
      i[0-9]*) envs=(HOP_SSA=sccp "HOP_SHAPE_K=${config#i}" HOP_PRUNE=1 "HOP_INLINE=${HOP_INLINE_SIZE:-30}") ;;
      a[0-9]*) envs=(HOP_SSA=sccp "HOP_SHAPE_K=${config#a}" HOP_PRUNE=1 HOP_IPA=1 "HOP_INLINE=${HOP_INLINE_SIZE:-30}") ;;
      j[0-9]*) envs=(HOP_SSA=sccp "HOP_SHAPE_K=${config#j}" HOP_PRUNE=1 HOP_IPA=1) ;;
      p[0-9]*) envs=(HOP_SSA=sccp "HOP_SHAPE_K=${config#p}" HOP_PRUNE=1) ;;
      k*) envs=(HOP_SSA=sccp "HOP_SHAPE_K=${config#k}") ;;
    esac
    asm="$WORK/$name.$config.s"; exe="$WORK/$name.$config"
    env "${envs[@]}" csi -R r7rs -I "$ROOT" -e \
      "(begin (load \"$ROOT/compiler.scm\") (write-aarch64-program-file \"$scaled\" \"$asm\"))"
    clang -arch arm64 -o "$exe" "$asm" "$ROOT/runtime.c" "$ROOT/codegen_harness.c"
    if ! HOP_HEAP_BYTES="$HEAP" "$exe" "$expected" >/dev/null 2>&1; then
      echo "WRONG RESULT: $name $config (expected $expected)" >&2; exit 1
    fi
    lines=$(grep -c '^\s' "$asm" || true)
    car=$(grep -c 'bl _hop_car' "$asm" || true)
    cdr=$(grep -c 'bl _hop_cdr' "$asm" || true)
    alloc=$(grep -c 'bl _hop_alloc_pair' "$asm" || true)
    stats="$(HOP_STATS=1 HOP_HEAP_BYTES="$HEAP" /usr/bin/time -l "$exe" 2>&1 >/dev/null || true)"
    dyn=$(sed -n 's/^hop-stats allocs=\([0-9]*\).*/\1/p' <<<"$stats")
    instrs=$(awk '/instructions retired/ {print $1}' <<<"$stats")
    printf '%-10s %-8s %6s %5s %5s %6s %12s %12s\n' "$name" "$config" "$lines" "$car" "$cdr" "$alloc" "$(( ${instrs:-0} - BASE ))" "${dyn:-0}"
  done
done
