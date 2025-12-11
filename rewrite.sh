#!/bin/bash
shopt -s globstar
OPTS="--filter lower_type_name --update-all";
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
parseFiles "build/*.sig"
parseFiles "build/*.fun"
parseFiles "build/*.sml"
parseFiles "TEST/*.sig"
parseFiles "TEST/*.fun"
parseFiles "TEST/*.sml"
