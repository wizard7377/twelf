#!/bin/bash
shopt -s globstar
OPTS=$@;
parse() {
    for i in {1..6}; do
        ast-grep scan $OPTS
    done 
}

parse 