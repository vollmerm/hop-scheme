ROOT := $(CURDIR)
SLD_FILES := $(shell find hop -name '*.sld')
CSI := csi -R r7rs -I $(ROOT)

.PHONY: build test repl example clean

# "build" for an interpreted compiler means: the generated include manifest
# is up to date and compiler.scm loads cleanly under it.
build: hop/includes.scm
	$(CSI) -e '(load "compiler.scm")' -e '(display "compiler.scm loaded OK\n")'

hop/includes.scm: $(SLD_FILES) tools/gen-includes.scm
	csi -s tools/gen-includes.scm hop > $@

test: hop/includes.scm
	./run_tests.sh

# Builds and runs the multi-file example under examples/ (a define-library
# unit plus a program that imports it) via build_program.sh, demonstrating
# how to drive a separate-compilation build outside of run_tests.sh.
example: hop/includes.scm
	mkdir -p out
	./build_program.sh -o out/vectors_demo examples/vectors_lib.scm examples/vectors_demo.scm
	./out/vectors_demo

# Drops into an interactive csi with every pass's exported bindings and the
# test fixtures in compiler_tests.scm live at the prompt.
repl: hop/includes.scm
	$(CSI) -e '(load "compiler.scm")' -e '(load "compiler_tests.scm")'

clean:
	rm -f hop/includes.scm
