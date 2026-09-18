#!/usr/bin/env bash
set -euo pipefail

# Compiles and links an ordered list of Scheme source files -- one or more
# define-library units followed by exactly one program unit -- into a single
# native executable, via compiler.scm's build-linked-program.
#
# Usage: ./build_program.sh -o OUTPUT_EXE SOURCE.scm [SOURCE.scm ...]
#
# Sources must be given in dependency order: each unit's imports must be
# satisfied by an earlier source on the command line. This compiler does no
# import-graph discovery or topological sorting -- see the "Compilation-unit
# driver" comment in compiler.scm -- so getting the order right is the
# caller's job, same as it is for build-linked-program itself.

ROOT="$(cd "$(dirname "$0")" && pwd)"

usage() {
  echo "Usage: $0 -o OUTPUT_EXE SOURCE.scm [SOURCE.scm ...]" >&2
  exit 1
}

output=""
sources=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -o)
      output="${2:-}"
      shift 2
      ;;
    *)
      sources+=("$1")
      shift
      ;;
  esac
done

if [[ -z "$output" || ${#sources[@]} -eq 0 ]]; then
  usage
fi

BUILD_DIR="$(mktemp -d)"
trap 'rm -rf "$BUILD_DIR"' EXIT

source_list=""
for src in "${sources[@]}"; do
  abs_src="$(cd "$(dirname "$src")" && pwd)/$(basename "$src")"
  source_list+="\"$abs_src\" "
done

csi -R r7rs -I "$ROOT" -e \
  "(begin (load \"$ROOT/compiler.scm\") (build-linked-program (list $source_list) \"$BUILD_DIR\"))"

manifest="$BUILD_DIR/build_manifest.txt"
objects=()
while IFS= read -r line; do
  objects+=("$line")
done <"$manifest"

clang -arch arm64 -I "$ROOT" -o "$output" "${objects[@]}" "$ROOT/runtime.c" "$ROOT/codegen_harness.c"

echo "Built $output"
