# Shared by the shell scripts (source it; needs ROOT set to the repo root).
# Picks the host Scheme that runs the Hop compiler -- Chicken or Guile -- and
# wraps how each one is invoked.
#
#   HOP_SCHEME=chicken|guile   force a host (default: Chicken if csi is on the
#                              PATH, else Guile)
#   HOP_CSC_FLAGS="-O3"       csc optimization flags for the compiled compiler
#                              (default -O2)
#   HOP_COMPILED=0             run the compiler from source (Chicken's
#                              interpreter) instead of the machine-code build
#
# hop_eval EXPR          run one expression, then exit
# hop_script FILE ARG..  run a script; (command-line) is (FILE ARG...)
# hop_repl EXPR          run EXPR, then stay at an interactive prompt
# hop_prepare_compiler   build/refresh the compiled compiler and set
#                        HOP_COMPILER (what to `load`) and HOP_LOAD (the
#                        expression that loads it); call it once before
#                        running the compiler many times. Without it, both
#                        refer to compiler.scm.

if [[ -z "${HOP_SCHEME:-}" ]]; then
  if command -v csi >/dev/null 2>&1; then
    HOP_SCHEME=chicken
  elif command -v guile >/dev/null 2>&1; then
    HOP_SCHEME=guile
  else
    echo "scheme.sh: neither csi (Chicken) nor guile found" >&2
    return 1 2>/dev/null || exit 1
  fi
fi
export HOP_SCHEME

HOP_COMPILER="$ROOT/compiler.scm"
HOP_LOAD="(load \"$HOP_COMPILER\")"

case "$HOP_SCHEME" in
  chicken)
    hop_eval() { csi -R r7rs -I "$ROOT" -e "$1"; }
    hop_script() { csi -R r7rs -I "$ROOT" -s "$@"; }
    hop_repl() { csi -R r7rs -I "$ROOT" -e "$1"; }
    # Interpreted code is many times slower than compiled, which matters for
    # anything that runs the compiler more than a few times.
    hop_prepare_compiler() {
      [[ "${HOP_COMPILED:-1}" == 0 ]] && return 0
      local dir="$ROOT/out/chicken" flags="${HOP_CSC_FLAGS:--O2}" so
      so="$dir/compiler${flags// /}.so"
      mkdir -p "$dir"
      if [[ ! -f "$so" ]] || [[ -n "$(find "$ROOT/compiler.scm" "$ROOT/hop" -name '*.s[cl][md]' -newer "$so" -print -quit)" ]]; then
        make -s -C "$ROOT" hop/includes.scm
        echo "compiling the compiler with csc..." >&2
        if ! (cd "$ROOT" && csc -s $flags -R r7rs compiler.scm -o "$so") >"$dir/build.log" 2>&1; then
          cat "$dir/build.log" >&2
          return 1
        fi
      fi
      HOP_COMPILER="$so"
      HOP_LOAD="(load \"$so\")"
    }
    ;;
  guile)
    # Guile compiles every file it loads to bytecode (cached under
    # out/guile-cache) and finds each hop library as hop/<name>.sld on -L.
    export GUILE_AUTO_COMPILE=1
    # Importing R7RS libraries into the user module warns about every core
    # binding they shadow, auto-compilation narrates itself, and a script that
    # loads the compiler at run time trips the unbound-variable lint; drop all three.
    guile_quiet() {
      local err rc
      err="$(mktemp)"
      "$@" 2>"$err" && rc=0 || rc=$?
      grep -avE 'imported module .* overrides core binding|imported from both|^;;; (note: |      |compil)|^;;; .*: warning: possibly unbound variable' "$err" >&2 || true
      rm -f "$err"
      return $rc
    }
    # guile-init.scm works around a Guile optimizer bug. Guile only compares
    # timestamps to decide whether a cached .go is current, so a stray plain
    # `guile -L .` would leave licm-miscompiled modules that these runs then
    # load. Keep our compiled files in a cache of their own.
    GUILE_CMD=(env XDG_CACHE_HOME="$ROOT/out/guile-cache"
               guile --r7rs -L "$ROOT" -l "$ROOT/tools/guile-init.scm")
    hop_eval() { guile_quiet "${GUILE_CMD[@]}" -c "$1"; }
    hop_script() { guile_quiet "${GUILE_CMD[@]}" -s "$@"; }
    hop_repl() { "${GUILE_CMD[@]}" -c "$1" -i; }
    hop_prepare_compiler() {
      # Compile once up front, so later (possibly parallel) runs only load.
      "${GUILE_CMD[@]}" -c "(load \"$ROOT/compiler.scm\")" >/dev/null 2>&1 </dev/null
    }
    ;;
  *)
    echo "scheme.sh: unknown HOP_SCHEME '$HOP_SCHEME' (want chicken or guile)" >&2
    return 1 2>/dev/null || exit 1
    ;;
esac
export HOP_COMPILER
export HOP_ROOT="$ROOT"
