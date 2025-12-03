
dune ?= dune 
RIPGREP ?= rg
RIPGREP_OPTS += -P --stats 
BAD_PATTERN := "(?<!module )\btype [A-Z]"
all: build test install
.PHONY: all build test install

build:
	$(dune) build

test:
	$(dune) runtest

install:
	$(dune) install

capitals:
	$(RIPGREP) $(RIPGREP_OPTS) --glob "*.ml" --glob "*.mli" $(BAD_PATTERN)