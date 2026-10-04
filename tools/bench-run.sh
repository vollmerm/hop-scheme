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
#   ioff             pruning and inlining, no SSA
# HOP_INLINE_SIZE (default 30) is the inlining size limit.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export HOP_CHECK_ALLOC=1
HEAP="${HOP_HEAP_BYTES:-67108864}"
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
files=("$@"); [[ ${#files[@]} -eq 0 ]] && files=("$ROOT"/bench/*.scm)

printf '%-10s %-8s %6s %5s %5s %6s %9s %9s\n' program config lines car cdr alloc allocs instrs
for f in "${files[@]}"; do
  name="$(basename "$f" .scm)"
  expected="$(csi -R r7rs -I "$ROOT" -s "$ROOT/tools/host-eval.scm" "$f")"
  for config in ${BENCH_CONFIGS:-off prune ioff i0 i1 i2 i3 i8}; do
    case "$config" in
      off) envs=(HOP_SSA=) ;;
      prune) envs=(HOP_SSA= HOP_PRUNE=1) ;;
      control) envs=(HOP_SSA=control) ;;
      ioff) envs=(HOP_SSA= HOP_PRUNE=1 "HOP_INLINE=${HOP_INLINE_SIZE:-30}") ;;
      i[0-9]*) envs=(HOP_SSA=sccp "HOP_SHAPE_K=${config#i}" HOP_PRUNE=1 "HOP_INLINE=${HOP_INLINE_SIZE:-30}") ;;
      p[0-9]*) envs=(HOP_SSA=sccp "HOP_SHAPE_K=${config#p}" HOP_PRUNE=1) ;;
      k*) envs=(HOP_SSA=sccp "HOP_SHAPE_K=${config#k}") ;;
    esac
    asm="$WORK/$name.$config.s"; exe="$WORK/$name.$config"
    env "${envs[@]}" csi -R r7rs -I "$ROOT" -e \
      "(begin (load \"$ROOT/compiler.scm\") (write-aarch64-program-file \"$f\" \"$asm\"))"
    clang -arch arm64 -o "$exe" "$asm" "$ROOT/runtime.c" "$ROOT/codegen_harness.c"
    if ! HOP_HEAP_BYTES="$HEAP" "$exe" "$expected" >/dev/null 2>&1; then
      echo "WRONG RESULT: $name $config (expected $expected)" >&2; exit 1
    fi
    lines=$(grep -c '^\s' "$asm" || true)
    car=$(grep -c 'bl _hop_car' "$asm" || true)
    cdr=$(grep -c 'bl _hop_cdr' "$asm" || true)
    alloc=$(grep -c 'bl _hop_alloc_pair' "$asm" || true)
    stats="$(HOP_HEAP_BYTES="$HEAP" /usr/bin/time -l "$exe" 2>&1 >/dev/null || true)"
    instrs=$(awk '/instructions retired/ {print $1}' <<<"$stats")
    printf '%-10s %-8s %6s %5s %5s %6s %9s %9s\n' "$name" "$config" "$lines" "$car" "$cdr" "$alloc" "-" "${instrs:-?}"
  done
done
