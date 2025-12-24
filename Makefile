DUNE ?= dune

SOURCES := $(wildcard lib/**/*.ml lib/**/*.mli)
.PHONY: build check sane test clean doc repl config

build: $(SOURCES)
	$(DUNE) build --profile release
check: $(SOURCES)
	$(DUNE) build --profile check
sane: $(SOURCES)
	$(DUNE) build --profile sane
test: $(SOURCES)
	$(DUNE) runtest
clean:
	$(DUNE) clean
doc: $(SOURCES)
	$(DUNE) build @doc
repl: $(SOURCES)
	$(DUNE) utop
config: sane
