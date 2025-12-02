
dune ?= dune 

all: build test install
.PHONY: all build test install

build:
	$(dune) build

test:
	$(dune) runtest

install:
	$(dune) install