#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

generate() {
  local test_name="$1"
  local asm_path="$2"
  HOP_SCHEME_SKIP_SAMPLES=1 guile --r7rs -c \
    "(load \"$ROOT/compiler.scm\") (write-named-aarch64-program '$test_name \"$asm_path\")"
}

build_and_run() {
  local test_name="$1"
  local expected="$2"
  local asm_path="$TMPDIR/${test_name}.s"
  local exe_path="$TMPDIR/${test_name}"

  generate "$test_name" "$asm_path"
  clang -arch arm64 -o "$exe_path" \
    "$asm_path" \
    "$ROOT/runtime.c" \
    "$ROOT/codegen_harness.c"
  "$exe_path" "$expected"
}

build_and_run test1 6
build_and_run test12 11
build_and_run test15 2
build_and_run test16 6
build_and_run test20 7
build_and_run test21 "()"
build_and_run test22 "#t"
build_and_run test23 "#t"
build_and_run test24 1
build_and_run test25 6

echo "codegen checks passed"
