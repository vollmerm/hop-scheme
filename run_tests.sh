#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

generate() {
  local test_name="$1"
  local asm_path="$2"
  csi -R r7rs -I "$ROOT" -e \
    "(begin (load \"$ROOT/compiler.scm\") (load \"$ROOT/compiler_tests.scm\") (write-named-aarch64-program '$test_name \"$asm_path\"))"
}

generate_all() {
  csi -R r7rs -I "$ROOT" -e \
    "(begin (load \"$ROOT/compiler.scm\") (load \"$ROOT/compiler_tests.scm\") (for-each (lambda (t) (write-named-aarch64-program (car t) (string-append \"$TMPDIR/\" (symbol->string (car t)) \".s\"))) named-tests))"
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
  csi -R r7rs -I "$ROOT" -e \
    "(begin (load \"$ROOT/compiler.scm\") (write-aarch64-program-file \"$source_path\" \"$asm_path\"))"
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

assert_compile_error() {
  local case_name="$1"
  local expected_pattern="$2"
  local source_text="$3"
  local source_path asm_path log_path
  source_path="$TMPDIR/$case_name.scm"
  asm_path="$(asm_path_for "$case_name")"
  log_path="$TMPDIR/$case_name.log"
  printf '%s\n' "$source_text" >"$source_path"
  if csi -R r7rs -I "$ROOT" -e \
    "(begin (load \"$ROOT/compiler.scm\") (write-aarch64-program-file \"$source_path\" \"$asm_path\"))" \
    >"$log_path" 2>&1; then
    printf 'unexpected compile success for %s\n' "$case_name" >&2
    exit 1
  fi
  if ! grep -Eq -e "$expected_pattern" "$log_path"; then
    printf 'missing compile error pattern for %s\n' "$case_name" >&2
    cat "$log_path" >&2
    exit 1
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

# Runs build-linked-program on an ordered list of source files (see
# compiler.scm), writing generated .s/.hopi/link_stub.c into
# $TMPDIR/$case_name.build, then assembles+links the resulting manifest into
# an executable at exe_path_for "$case_name".
build_multi_file_case() {
  local case_name="$1"
  shift
  local out_dir exe_path source_list src
  out_dir="$TMPDIR/$case_name.build"
  exe_path="$(exe_path_for "$case_name")"
  mkdir -p "$out_dir"
  source_list=""
  for src in "$@"; do
    source_list+="\"$src\" "
  done
  csi -R r7rs -I "$ROOT" -e \
    "(begin (load \"$ROOT/compiler.scm\") (build-linked-program (list $source_list) \"$out_dir\"))"
  local objects=()
  while IFS= read -r line; do
    objects+=("$line")
  done <"$out_dir/build_manifest.txt"
  clang -arch arm64 -I "$ROOT" -o "$exe_path" "${objects[@]}" "$ROOT/runtime.c" "$ROOT/codegen_harness.c"
}

assert_multi_file_output() {
  local case_name="$1"
  local expected="$2"
  shift 2
  local exe_path
  exe_path="$(exe_path_for "$case_name")"
  build_multi_file_case "$case_name" "$@"
  "$exe_path" "$expected" >/dev/null
  printf 'ok %s\n' "$case_name"
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
  "test36|1275|4096"
  "test37|8"
  "test38|#t"
  "test39|3"
  "test40|16"
  "test41|1830|2048"
  "test42|7|2048"
  "test43|7|2048"
  "test44|7|1024"
  "test45|36"
  "test46|2"
  "test47|5"
  "test48|11"
  "test49|6"
  "test50|9"
  "test51|6"
  "test52|6"
  "test53|9"
  "test54|5"
  "test55|7"
  "test56|7"
  "test57|3"
  "test58|8"
  "test59|0"
  "test60|42"
  "test61|5"
  "test62|2"
  "test63|7"
  "test64|5"
  "test65|42|2048"
  "test66|42"
  "test67|42"
  "test68|1"
  "test69|1"
  "test70|10"
  "test71|30"
  "test72|foo"
  "test73|1"
  "test74|10"
  "test75|42"
  "test76|a"
  "test77|b"
  "test78|2"
  "test79|5"
  "test80|3"
  "test81|120"
  "test82|symbol"
  "test83|yes"
  "test84|25"
  "test85|vowel"
  "test86|16"
  "test87|7"
  "test88|3"
  "test89|2"
  "test90|200"
  "test91|10"
  "test92|6"
  "test93|42"
  "test94|3"
  "test95|6"
  "test96|11"
  "test97|15"
  "test98|30"
  "test99|12"
  "test100|100"
  "test101|20"
  "test102|10"
  "test103|30"
  "test104|62"
  "test105|44"
)

generate_all

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
assert_asm_not_contains "test48" '_hop_car' 'safe car helper for direct pair allocation'
assert_asm_not_contains "test49" '_hop_car' 'safe car helper for pair?-guarded then branch'
assert_asm_contains "test50" '_hop_car' 'safe car helper for conservative join'
assert_asm_not_contains "test51" '_hop_car' 'safe car after back-edge pair propagation via internal-only step'
assert_asm_not_contains "test51" '_hop_cdr' 'safe cdr after back-edge pair propagation via internal-only step'
assert_asm_contains "test52" '_hop_car' "B's car is conservatively preserved (only A's car is proven safe)"
assert_asm_not_contains "test52" '_hop_cdr' 'all cdr operations in A are proven safe after two iterations'
assert_asm_contains "test5" '\bx(19|20|21|22|23|24|25|26|27|28)\b' 'callee-saved register allocation'
assert_asm_not_contains "test16" '\bx23\b' 'uncoalesced temporary register in recursive loop'
assert_asm_not_contains "test5" 'str x9, \[sp, #(24|32|40)\]' 'eager root shadow writes without safepoints'

# variadic known-call fast path: the overflow args are consed at compile
# time and the call itself is still a direct label branch, exactly like an
# ordinary fixed-arity known-call -- no runtime dispatch helper at all.
# (test91 itself also contains sum-list's own self-recursive call, which
# is -- independent of variadic support -- not resolved to a known-call by
# 0CFA, so the "no generic call helper anywhere" check belongs on test95,
# a minimal program with nothing else that could call indirectly.)
assert_asm_contains "test91" 'b(l)? _cfa\.proc\.[0-9]+' 'direct closure call lowering for variadic known-call'
assert_asm_contains "test95" 'b(l)? _cfa\.proc\.[0-9]+' 'direct closure call lowering for variadic known-call'
assert_asm_not_contains "test95" '_hop_(tail_)?call_[0-9]+' 'generic call helper'

# Cluster fallback dispatch: with two externally-callable members
# (even? and odd?), the shared cluster-proc must branch on the runtime
# entry-tag rather than collapsing to an unconditional jump to whichever
# member happens to be first (see test96's definition for why a broken
# dispatch would still "run" but produce the wrong answer).
assert_asm_contains "test96" 'b\.ne Lentry\.' 'conditional entry-tag dispatch branch between cluster members'

# indirect call to a statically-unresolvable variadic target must go
# through the runtime's hop_call_N family (which internally branches on the
# closure's variadic-ness) -- there is no way to lower this to a direct
# label call.
assert_asm_contains "test92" '_hop_(tail_)?call_[0-9]+' 'generic call helper for indirect variadic target'

# apply's argument count is only known at run time even when its target is
# statically known, so it can never take the known-call fast path: it
# always lowers to the single fixed hop_apply entry point.
assert_asm_contains "test94" '_hop_apply' 'apply always lowers through hop_apply, never a direct call'
# Anchored to leading instruction indentation so this doesn't spuriously
# match the unrelated ".globl _cfa.proc.N" export directive every compiled
# procedure emits (that line begins at column 0, not indented).
assert_asm_not_contains "test94" '^    b(l)? _cfa\.proc\.[0-9]+' 'apply never becomes a direct closure call'

# constant folding: x*x with x=3 must collapse to an immediate load, no multiply
assert_asm_not_contains "test53" '\bmul\b' 'constant-folded multiplication eliminated'
# dead write elimination: the unused (+ x 1) in the lambda must not emit an add
assert_asm_not_contains "test54" '\badd x[0-9]+, x[0-9]+, x[0-9]+\b' 'dead-write add instruction eliminated'

# safe arithmetic: literal-operand cases are optimized away entirely
assert_asm_not_contains "test55" '_hop_safe_add' 'safe-+ of literals optimized to inline add'
assert_asm_not_contains "test56" '_hop_safe_add' 'safe-+ with let-bound literal optimized'
# car result is not proven fixnum, so the runtime check must remain
assert_asm_contains "test57" '_hop_safe_add' 'safe-+ preserved when operand is car result'
# result of safe arith is proven fixnum, so outer safe-+ is also optimized
assert_asm_not_contains "test58" '_hop_safe_add' 'safe-+ of safe-arith result optimized'

# arbitrary-argument arithmetic constant folding & apply lowering
assert_asm_not_contains "test97" '\badd x[0-9]+, x[0-9]+, x[0-9]+\b' 'constant-folded arbitrary-argument addition eliminated'
assert_asm_not_contains "test97" '_hop_safe_add' 'safe-+ eliminated in constant-folded addition'
assert_asm_not_contains "test98" '\bmul\b' 'constant-folded arbitrary-argument multiplication eliminated'
assert_asm_not_contains "test98" '_hop_safe_mul' 'safe-* eliminated in constant-folded multiplication'
assert_asm_not_contains "test99" '\bsub x[0-9]+, x[0-9]+, x[0-9]+\b' 'constant-folded arbitrary-argument subtraction eliminated'
assert_asm_not_contains "test99" '_hop_safe_sub' 'safe-- eliminated in constant-folded subtraction'
assert_asm_not_contains "test100" '_hop_safe_add' 'arbitrary-argument addition with known fixnums lowers to inline add'
assert_asm_contains "test101" '_hop_apply' 'apply of + lowers through hop_apply'
assert_asm_contains "test104" '_hop_apply' 'apply of - lowers through hop_apply'

assert_file_output \
  "file-test1" \
  "42" \
  $'(define base 40)\n(begin (define bump (lambda (x) (primop + base x))))\n(app bump 2)'

assert_file_output \
  "file-quote1" \
  "b" \
  $'(define lst (quote (a b)))\n(car (cdr lst))'

assert_file_output \
  "file-quote2" \
  "y" \
  $'(car (cdr \'(x y)))'

assert_file_output \
  "file-surface1" \
  "3" \
  $'(define (len xs)\n  (if (null? xs) 0 (+ 1 (len (cdr xs)))))\n(len \'(a b c))'

# A miniature tree rewriter in plain surface Scheme: quoted symbol data,
# eq? dispatch via cond, structural recursion, bare applications. This is the
# shape of a compiler pass, which is what self-hosting ultimately needs.
assert_file_output \
  "file-surface2" \
  "new" \
  $'(define (rename-tree x)\n  (cond ((null? x) \'())\n        ((pair? x) (cons (rename-tree (car x)) (rename-tree (cdr x))))\n        ((eq? x \'old) \'new)\n        (else x)))\n(car (rename-tree \'(old other)))'

assert_compile_error \
  "file-letrec-init-read" \
  'letrec init cannot read recursive bindings during initialization' \
  $'(letrec ((x 1)\n          (y x))\n   y)'

# (define (f . args) ...) surface sugar for an all-rest lambda.
assert_file_output \
  "file-variadic-all-rest" \
  "1" \
  $'(define (my-list . xs) xs)\n(car (my-list 1 2 3))'

# (define (f a . rest) ...) surface sugar for fixed params + a rest param.
assert_file_output \
  "file-variadic-fixed-and-rest" \
  "3" \
  $'(define (f a . rest) (+ a (car rest)))\n(f 1 2 3)'

# A known call site (f referenced directly) supplying fewer arguments than
# f's fixed parameter count is a provably-wrong program: (hop pass cfa)
# catches it at compile time rather than deferring to a runtime panic.
assert_compile_error \
  "file-variadic-too-few-args" \
  'Too few arguments to variadic procedure' \
  $'(define (f a b . rest) (+ a b))\n(f 1)'

# Zero-argument subtraction is a syntax error.
assert_compile_error \
  "file-sub-zero-args" \
  '- requires at least 1 argument' \
  $'(-)'

# Surface arbitrary-argument arithmetic in file scope.
assert_file_output \
  "file-arith-variadic" \
  "100" \
  $'(define (sum4 a b c d) (+ a b c d))\n(sum4 10 20 30 40)'

# --- Multi-file build (define-library / import / separate compilation) ----
# Exercises build-linked-program end to end: a library unit and a program
# unit that imports it, compiled separately and linked together via a
# generated C stub (see compiler.scm's "Linking" and "Multi-file build
# driver" sections).

multi_lib_path="$TMPDIR/multi-lib.scm"
multi_prog_path="$TMPDIR/multi-prog.scm"
printf '%s\n' \
  '(define-library (multitest)' \
  '  (export add1)' \
  '  (begin' \
  '    (define (bump-by n step) (+ n step))' \
  '    (define (add1 n) (bump-by n 1))))' \
  >"$multi_lib_path"
printf '%s\n' \
  '(import (multitest))' \
  '(add1 41)' \
  >"$multi_prog_path"

assert_multi_file_output "multi-file-basic" "42" "$multi_lib_path" "$multi_prog_path"

# The exported binding (add1) keeps .globl visibility; the internal,
# non-exported binding (bump-by) must not -- it gets .private_extern instead,
# so it never leaks into the linked executable's public symbol table (the
# fix in hop/backend.sld's emit-global-cells).
multi_build_dir="$TMPDIR/multi-file-basic.build"
if ! grep -Eq '^\.globl _hop_g_.*add1$' "$multi_build_dir"/*.s; then
  printf 'missing .globl on exported binding in %s\n' "$multi_build_dir" >&2
  exit 1
fi
if ! grep -Eq '^\.private_extern _hop_g_.*bump' "$multi_build_dir"/*.s; then
  printf 'missing .private_extern on internal binding in %s\n' "$multi_build_dir" >&2
  exit 1
fi
if grep -Eq '^\.globl _hop_g_.*bump' "$multi_build_dir"/*.s; then
  printf 'internal binding unexpectedly kept .globl visibility in %s\n' "$multi_build_dir" >&2
  exit 1
fi
printf 'ok multi-file-visibility\n'

# A unit whose declared import isn't satisfied by any earlier unit in the
# build order is a clear compile-time error, not a downstream codegen
# failure resolving a free reference.
multi_bad_prog_path="$TMPDIR/multi-bad-prog.scm"
printf '%s\n' \
  '(import (does-not-exist))' \
  '(add1 41)' \
  >"$multi_bad_prog_path"
multi_bad_out_dir="$TMPDIR/multi-file-unresolved-import.build"
multi_bad_log="$TMPDIR/multi-file-unresolved-import.log"
mkdir -p "$multi_bad_out_dir"
if csi -R r7rs -I "$ROOT" -e \
  "(begin (load \"$ROOT/compiler.scm\") (build-linked-program (list \"$multi_lib_path\" \"$multi_bad_prog_path\") \"$multi_bad_out_dir\"))" \
  >"$multi_bad_log" 2>&1; then
  printf 'unexpected compile success for multi-file-unresolved-import\n' >&2
  exit 1
fi
if ! grep -Eq 'Unresolved import' "$multi_bad_log"; then
  printf 'missing expected error for multi-file-unresolved-import\n' >&2
  cat "$multi_bad_log" >&2
  exit 1
fi
printf 'ok multi-file-unresolved-import\n'

echo "compiler tests passed"
