#!/bin/bash

# Script to apply all module type renamings from fixes.md
# Usage: ./apply_fixes.sh [--dry-run]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_DIR="$SCRIPT_DIR/lib"
FIXES_FILE="$SCRIPT_DIR/fixes.md"

DRY_RUN=false
if [[ "$1" == "--dry-run" ]]; then
    DRY_RUN=true
    echo "DRY RUN MODE - No files will be modified"
    echo ""
fi

if [[ ! -f "$FIXES_FILE" ]]; then
    echo "Error: $FIXES_FILE not found"
    exit 1
fi

if [[ ! -d "$LIB_DIR" ]]; then
    echo "Error: $LIB_DIR directory not found"
    exit 1
fi

echo "Parsing $FIXES_FILE..."
echo ""

files_modified=0
total_replacements=0

while IFS= read -r line; do
    # Skip empty lines
    [[ -z "$line" ]] && continue
    
    # Parse the line format:
    # Outside of `./lib/path/file.ml` change each occurence of `OLD` to `NEW`
    if [[ $line =~ Outside\ of\ \`([^`]+)\`\ change\ each\ occurence\ of\ \`([^`]+)\`\ to\ \`([^`]+)\` ]]; then
        excluded_file="${BASH_REMATCH[1]}"
        old_pattern="${BASH_REMATCH[2]}"
        new_pattern="${BASH_REMATCH[3]}"
        
        echo "Processing: $old_pattern → $new_pattern"
        echo "  Excluding: $excluded_file"
        
        # Find all .ml files except the excluded one
        rule_replacements=0
        rule_files=0
        
        while IFS= read -r -d '' file; do
            # Skip the excluded file
            excluded_path="$SCRIPT_DIR/$excluded_file"
            if [[ "$(realpath "$file")" == "$(realpath "$excluded_path")" ]]; then
                continue
            fi
            
            # Count occurrences using grep (word boundaries)
            count=$(grep -o "\b$old_pattern\b" "$file" 2>/dev/null | wc -l || echo 0)
            
            if [[ $count -gt 0 ]]; then
                echo "    $(realpath --relative-to="$LIB_DIR" "$file"): $count replacement(s)"
                
                if [[ "$DRY_RUN" == false ]]; then
                    # Use sed with word boundaries for replacement
                    # Create a backup, then do the replacement
                    sed -i.bak "s/\b$old_pattern\b/$new_pattern/g" "$file"
                    rm -f "$file.bak"
                fi
                
                ((rule_files++))
                ((rule_replacements+=count))
            fi
        done < <(find "$LIB_DIR" -name "*.ml" -type f -print0)
        
        if [[ $rule_files -gt 0 ]]; then
            echo "  Files modified: $rule_files, Replacements: $rule_replacements"
            ((files_modified+=rule_files))
            ((total_replacements+=rule_replacements))
        fi
        echo ""
    fi
done < "$FIXES_FILE"

echo "========================================"
echo "Summary:"
echo "  Files modified: $files_modified"
echo "  Total replacements: $total_replacements"

if [[ "$DRY_RUN" == true ]]; then
    echo ""
    echo "(DRY RUN - no files were actually modified)"
fi
