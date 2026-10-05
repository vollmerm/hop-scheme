#!/usr/bin/env bash
# Differential test for the structural cons analysis: random programs are
# compiled with the analysis off and at several depths, run, and compared with
# the host Scheme's answer.
#   tools/fuzz-shapes.sh [COUNT] [SEED] [DEPTHS...]
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
. "$ROOT/tools/scheme.sh"
hop_prepare_compiler
COUNT="${1:-40}"
SEED="${2:-1}"
shift $(( $# > 2 ? 2 : $# )) || true
DEPTHS=("${@:-0 1 2 3 8}")
read -r -a DEPTHS <<< "${DEPTHS[*]}"

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
export HOP_CHECK_ALLOC=1

hop_script "$ROOT/tools/fuzz-shapes.scm" gen "$WORK" "$COUNT" "$SEED"

failures=0
run_config() {
  local label="$1"; shift
  local dir="$WORK/$label"
  mkdir -p "$dir"
  cp "$WORK"/p*.scm "$dir"/
  (export "$@"; hop_script "$ROOT/tools/fuzz-shapes.scm" compile "$dir")
  for ((i = 0; i < COUNT; i++)); do
    clang -arch arm64 -o "$dir/p$i" "$dir/p$i.s" "$ROOT/runtime.c" "$ROOT/codegen_harness.c"
    if ! "$dir/p$i" "$(cat "$WORK/p$i.expected")" >/dev/null 2>&1; then
      printf 'MISMATCH %s program %s (seed %s): expected %s\n' \
        "$label" "$i" "$SEED" "$(cat "$WORK/p$i.expected")" >&2
      cp "$WORK/p$i.scm" "/tmp/fuzz-failure-$label-$SEED-$i.scm"
      failures=$((failures + 1))
    fi
  done
}

run_config off HOP_SSA=
for k in "${DEPTHS[@]}"; do
  run_config "k$k" HOP_SSA=sccp HOP_SHAPE_K="$k"
done

if (( failures > 0 )); then
  printf '%d mismatches\n' "$failures" >&2
  exit 1
fi
printf 'fuzz ok: %d programs, seed %s, configs off %s\n' "$COUNT" "$SEED" "${DEPTHS[*]}"
