ROOT := $(CURDIR)
SLD_FILES := $(shell find hop -name '*.sld')
CSI := csi -R r7rs -I $(ROOT)

.PHONY: build test repl clean

# "build" for an interpreted compiler means: the generated include manifest
# is up to date and compiler.scm loads cleanly under it.
build: hop/includes.scm
	$(CSI) -e '(load "compiler.scm")' -e '(display "compiler.scm loaded OK\n")'

hop/includes.scm: $(SLD_FILES) tools/gen-includes.scm
	csi -s tools/gen-includes.scm hop > $@

test: hop/includes.scm
	./run_tests.sh

# Drops into an interactive csi with every pass's exported bindings and the
# test fixtures in compiler_tests.scm live at the prompt.
repl: hop/includes.scm
	$(CSI) -e '(load "compiler.scm")' -e '(load "compiler_tests.scm")'

clean:
	rm -f hop/includes.scm
