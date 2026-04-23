#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

generate() {
  local test_name="$1"
  local asm_path="$2"
  guile --r7rs -c \
    "(load \"$ROOT/compiler.scm\") (load \"$ROOT/compiler_tests.scm\") (write-named-aarch64-program '$test_name \"$asm_path\")"
}

asm_path_for() {
  printf '%s/%s.s\n' "$TMPDIR" "$1"
}

exe_path_for() {
  printf '%s/%s\n' "$TMPDIR" "$1"
}

ensure_asm() {
  local test_name="$1"
  local asm_path
  asm_path="$(asm_path_for "$test_name")"
  if [[ ! -f "$asm_path" ]]; then
    generate "$test_name" "$asm_path"
  fi
}

build_executable() {
  local test_name="$1"
  local asm_path exe_path
  asm_path="$(asm_path_for "$test_name")"
  exe_path="$(exe_path_for "$test_name")"
  ensure_asm "$test_name"
  clang -arch arm64 -o "$exe_path" \
    "$asm_path" \
    "$ROOT/runtime.c" \
    "$ROOT/codegen_harness.c"
}

assert_output() {
  local test_name="$1"
  local expected="$2"
  local heap_bytes="${3:-}"
  local exe_path
  exe_path="$(exe_path_for "$test_name")"
  build_executable "$test_name"
  if [[ -n "$heap_bytes" ]]; then
    HOP_HEAP_BYTES="$heap_bytes" "$exe_path" "$expected" >/dev/null
  else
    "$exe_path" "$expected" >/dev/null
  fi
  printf 'ok %s\n' "$test_name"
}

assert_file_output() {
  local case_name="$1"
  local expected="$2"
  local source_text="$3"
  local heap_bytes="${4:-}"
  local source_path asm_path exe_path
  source_path="$TMPDIR/$case_name.scm"
  asm_path="$(asm_path_for "$case_name")"
  exe_path="$(exe_path_for "$case_name")"
  printf '%s\n' "$source_text" >"$source_path"
  guile --r7rs -c \
    "(load \"$ROOT/compiler.scm\") (write-aarch64-program-file \"$source_path\" \"$asm_path\")"
  clang -arch arm64 -o "$exe_path" \
    "$asm_path" \
    "$ROOT/runtime.c" \
    "$ROOT/codegen_harness.c"
  if [[ -n "$heap_bytes" ]]; then
    HOP_HEAP_BYTES="$heap_bytes" "$exe_path" "$expected" >/dev/null
  else
    "$exe_path" "$expected" >/dev/null
  fi
  printf 'ok %s\n' "$case_name"
}

assert_asm_contains() {
  local test_name="$1"
  local pattern="$2"
  local description="$3"
  local asm_path
  asm_path="$(asm_path_for "$test_name")"
  ensure_asm "$test_name"
  if ! grep -Eq "$pattern" "$asm_path"; then
    printf 'missing %s in %s\n' "$description" "$test_name" >&2
    exit 1
  fi
}

assert_asm_not_contains() {
  local test_name="$1"
  local pattern="$2"
  local description="$3"
  local asm_path
  asm_path="$(asm_path_for "$test_name")"
  ensure_asm "$test_name"
  if grep -Eq "$pattern" "$asm_path"; then
    printf 'unexpected %s in %s\n' "$description" "$test_name" >&2
    exit 1
  fi
}

runtime_cases=(
  "test1|6"
  "test2|6"
  "test3|1"
  "test5|15"
  "test8|2"
  "test9|8"
  "test10|15"
  "test11|6"
  "test12|11"
  "test13|0"
  "test14|#t"
  "test15|2"
  "test16|6"
  "test17|1"
  "test18|#t"
  "test19|#<closure>"
  "test20|7"
  "test21|()"
  "test22|#t"
  "test23|#t"
  "test24|1"
  "test25|6"
  "test26|6"
  "test27|6"
  "test28|6"
  "test29|3"
  "test30|5"
  "test31|2"
  "test32|2"
  "test33|7"
  "test34|6"
  "test35|1830|2048"
  "test36|1275|2048"
  "test37|8"
  "test38|#t"
  "test39|3"
  "test40|16"
  "test41|1830|2048"
  "test42|7|2048"
  "test43|7|2048"
)

for case in "${runtime_cases[@]}"; do
  IFS='|' read -r test_name expected heap_bytes <<<"$case"
  assert_output "$test_name" "$expected" "${heap_bytes:-}"
done

assert_asm_contains "test26" 'b(l)? _cfa\.proc\.[0-9]+' 'direct closure call lowering'
assert_asm_not_contains "test26" '_hop_(tail_)?call_[0-9]+' 'generic call helper'

assert_asm_contains "test27" '_hop_(tail_)?call_[0-9]+' 'generic call helper'

assert_asm_contains "test28" 'b(l)? _cfa\.proc\.[0-9]+' 'nested direct closure call lowering'
assert_asm_not_contains "test28" '_hop_(tail_)?call_[0-9]+' 'generic call helper'

assert_asm_contains "test33" '_hop_(tail_)?call_[0-9]+' 'polymorphic captured closure helper'
assert_asm_contains "test5" '\bx(19|20|21|22|23|24|25|26|27|28)\b' 'callee-saved register allocation'

assert_file_output \
  "file-test1" \
  "42" \
  $'(define base 40)\n(begin (define bump (lambda (x) (primop + base x))))\n(app bump 2)'

echo "compiler tests passed"
