#!/bin/bash
# Automated Currying Converter Script
# Converts uncurried functions to curried form in OCaml files

if [ $# -eq 0 ]; then
    echo "Usage: $0 <file1.ml> <file2.ml> ..."
    exit 1
fi

for file in "$@"; do
    echo "Converting $file..."

    # Create backup
    cp "$file" "$file.backup"

    # Convert: fun (x, y) -> body  to  fun x y -> body
    # Pattern 1: Simple two-parameter tuple
    sed -i 's/fun (\([a-zA-Z_][a-zA-Z0-9_'"'"']*\), *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\)) *->/fun \1 \2 ->/g' "$file"

    # Pattern 2: Three-parameter tuple
    sed -i 's/fun (\([a-zA-Z_][a-zA-Z0-9_'"'"']*\), *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\), *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\)) *->/fun \1 \2 \3 ->/g' "$file"

    # Convert: let f (x, y) = body  to  let f x y = body
    # Pattern 3: let rec with two params
    sed -i 's/let  *rec  *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\)  *(\([a-zA-Z_][a-zA-Z0-9_'"'"']*\),  *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\))  *=/let rec \1 \2 \3 =/g' "$file"

    # Pattern 4: let rec with three params
    sed -i 's/let  *rec  *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\)  *(\([a-zA-Z_][a-zA-Z0-9_'"'"']*\),  *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\),  *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\))  *=/let rec \1 \2 \3 \4 =/g' "$file"

    # Pattern 5: let without rec, two params
    sed -i 's/let  *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\)  *(\([a-zA-Z_][a-zA-Z0-9_'"'"']*\),  *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\))  *=/let \1 \2 \3 =/g' "$file"

    # Pattern 6: let without rec, three params
    sed -i 's/let  *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\)  *(\([a-zA-Z_][a-zA-Z0-9_'"'"']*\),  *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\),  *\([a-zA-Z_][a-zA-Z0-9_'"'"']*\))  *=/let \1 \2 \3 \4 =/g' "$file"

    echo "Converted $file (backup saved as $file.backup)"
done

echo "Done! Review the changes and test the build."
echo "To restore from backups: for f in *.backup; do mv \"\$f\" \"\${f%.backup}\"; done"
