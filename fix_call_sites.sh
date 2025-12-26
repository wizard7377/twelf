#!/bin/bash
# Script to fix call sites of curried functions
# Extracts function names from git diff and updates their call sites

if [ $# -eq 0 ]; then
    echo "Usage: $0 <file1.ml> <file2.ml> ..."
    echo "   or: $0 --auto  (automatically process all modified files)"
    exit 1
fi

# Function to extract converted function names from a backup file
extract_converted_functions() {
    local file=$1
    local backup="${file}.backup"

    if [ ! -f "$backup" ]; then
        return
    fi

    # Find functions converted from (x, y) to x y
    diff "$backup" "$file" 2>/dev/null | \
        grep "^<.*let.*rec.*(" | \
        sed 's/^<.*let.*rec *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\).*/\1/' | \
        sort -u
}

# Function to fix call sites in a file for a given function name
fix_call_sites() {
    local file=$1
    local funcname=$2

    # Pattern: funcname (arg1, arg2) -> funcname arg1 arg2
    # This is tricky because we need to preserve nested expressions
    # Start with simple cases

    # Two arguments: func (a, b)
    sed -i 's/\b'"${funcname}"' *(\([a-zA-Z_][a-zA-Z0-9_'"'"']*\), *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\))/'"${funcname}"' \1 \2/g' "$file"

    # Three arguments: func (a, b, c)
    sed -i 's/\b'"${funcname}"' *(\([a-zA-Z_][a-zA-Z0-9_'"'"']*\), *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\), *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\))/'"${funcname}"' \1 \2 \3/g' "$file"
}

if [ "$1" = "--auto" ]; then
    # Process all .ml files that have .backup files
    for backup in $(find lib -name "*.ml.backup" 2>/dev/null); do
        file="${backup%.backup}"
        echo "Processing $file..."

        # Extract function names that were converted
        funcs=$(extract_converted_functions "$file")

        # For each converted function, fix its call sites
        for func in $funcs; do
            if [ -n "$func" ]; then
                echo "  Fixing calls to: $func"
                fix_call_sites "$file" "$func"
            fi
        done
    done
else
    # Process specified files
    for file in "$@"; do
        if [ ! -f "$file" ]; then
            echo "File not found: $file"
            continue
        fi

        echo "Processing $file..."

        # Extract and fix
        funcs=$(extract_converted_functions "$file")
        for func in $funcs; do
            if [ -n "$func" ]; then
                echo "  Fixing calls to: $func"
                fix_call_sites "$file" "$func"
            fi
        done
    done
fi

echo "Done! Review the changes before committing."
