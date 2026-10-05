ROOT := $(CURDIR)
SLD_FILES := $(shell find hop -name '*.sld')

# The host Scheme that runs the compiler: chicken or guile. Defaults to Chicken
# when csi is on the PATH, else Guile; override with `make HOP_SCHEME=guile ...`.
# tools/scheme.sh holds the per-host command lines.
export HOP_SCHEME ?= $(shell command -v csi >/dev/null 2>&1 && echo chicken || echo guile)
COUNT ?= 40
SEED ?= 1
WITH_SCHEME := ROOT=$(ROOT); . tools/scheme.sh;

.DELETE_ON_ERROR:
.PHONY: build compiler test fuzz repl example dump clean

# "build" for an interpreted compiler means: the generated include manifest
# is up to date and compiler.scm loads cleanly under it. (Only Chicken uses the
# manifest; Guile finds each library as hop/<name>.sld on its load path.)
build: hop/includes.scm
	@$(WITH_SCHEME) hop_eval '(begin (load "compiler.scm") (display "compiler.scm loaded OK ($(HOP_SCHEME))\n"))'

hop/includes.scm: $(SLD_FILES) tools/gen-includes.scm
	@$(WITH_SCHEME) hop_script tools/gen-includes.scm $(SLD_FILES) > $@

# Compiles the compiler to machine code, the way the test, fuzz, and bench
# scripts run it: with csc under Chicken (out/chicken/compiler-O2.so; override
# the flags with HOP_CSC_FLAGS), and to cached bytecode under Guile.
compiler: hop/includes.scm
	@$(WITH_SCHEME) hop_prepare_compiler

test: hop/includes.scm
	./run_tests.sh

# Differential fuzzing of the cons analysis; see tools/fuzz-shapes.sh.
# e.g. `make fuzz COUNT=200 SEED=7`
fuzz: hop/includes.scm
	./tools/fuzz-shapes.sh $(COUNT) $(SEED)

# Builds and runs the multi-file example under examples/ (a define-library
# unit plus a program that imports it) via build_program.sh, demonstrating
# how to drive a separate-compilation build outside of run_tests.sh.
example: hop/includes.scm
	mkdir -p out
	./build_program.sh -o out/vectors_demo examples/vectors_lib.scm examples/vectors_demo.scm
	./out/vectors_demo

# Drops into an interactive prompt with every pass's exported bindings and the
# test fixtures in compiler_tests.scm live at the prompt.
repl: hop/includes.scm
	@$(WITH_SCHEME) hop_repl '(begin (load "compiler.scm") (load "compiler_tests.scm"))'

# Prints the CFG (or STAGE=machine allocated code) for a source file or a
# compiler_tests.scm fixture, e.g. `make dump T=test34`.
dump: hop/includes.scm
	@$(WITH_SCHEME) hop_script tools/dump-cfg.scm $(T) $(STAGE)

clean:
	rm -f hop/includes.scm
	rm -rf out/chicken out/guile-cache
