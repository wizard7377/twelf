#!/bin/bash

OPTS="--inspect summary --filter lower_type_name";
parse() {
    local file=$1
    # echo "ast-grep scan $OPTS $file"
    ast-grep scan $OPTS $file
}
parseFiles() {
    local files=$1
    for file in $files; do
        parse $file
    done
}
parseFiles "src/**/*.sig"
parseFiles "src/**/*.fun"
parseFiles "src/**/*.sml"
