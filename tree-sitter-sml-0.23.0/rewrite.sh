#!/bin/bash

parse() {
    local file=$1
    tree-sitter parse $file
}

parseFiles() {
    local files=$1
    for file in $files; do
        echo "Parsing $file"
        parse $file
    done
}
parseFiles "../**/*.sig"

