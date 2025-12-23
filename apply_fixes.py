#!/usr/bin/env python3
"""
Script to automatically apply all module type renamings described in fixes.md
"""

import re
import os
from pathlib import Path


def parse_fixes_file(fixes_path):
    """Parse the fixes.md file and extract transformation rules."""
    rules = []
    
    with open(fixes_path, 'r') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            
            # Pattern: Outside of `./lib/path/file.ml` change each occurence of `OLD` to `NEW`
            match = re.match(
                r"Outside of `(\./lib/[^`]+)` change each occurence of `([^`]+)` to `([^`]+)`",
                line
            )
            
            if match:
                excluded_file = match.group(1)
                old_pattern = match.group(2)
                new_pattern = match.group(3)
                
                rules.append({
                    'excluded_file': excluded_file,
                    'old_pattern': old_pattern,
                    'new_pattern': new_pattern
                })
    
    return rules


def apply_replacements(lib_dir, rules, dry_run=False):
    """Apply the replacement rules to all .ml files in lib directory."""
    stats = {
        'files_processed': 0,
        'files_modified': 0,
        'total_replacements': 0
    }
    
    # Get all .ml files in lib directory
    ml_files = list(Path(lib_dir).rglob('*.ml'))
    
    for rule in rules:
        excluded_file_path = Path(rule['excluded_file'])
        old_pattern = rule['old_pattern']
        new_pattern = rule['new_pattern']
        
        # Create a word boundary regex pattern to match whole words only
        # This ensures we don't replace partial matches
        pattern = re.compile(r'\b' + re.escape(old_pattern))
        
        files_changed_for_rule = 0
        replacements_for_rule = 0
        
        for ml_file in ml_files:
            # Skip the excluded file
            if ml_file.resolve() == excluded_file_path.resolve():
                continue
            
            try:
                with open(ml_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # Count how many replacements would be made
                matches = pattern.findall(content)
                if not matches:
                    continue
                
                # Perform the replacement
                new_content = pattern.sub(new_pattern, content)
                
                if new_content != content:
                    if not dry_run:
                        with open(ml_file, 'w', encoding='utf-8') as f:
                            f.write(new_content)
                    
                    num_replacements = len(matches)
                    files_changed_for_rule += 1
                    replacements_for_rule += num_replacements
                    
                    print(f"  {ml_file.relative_to(lib_dir)}: {num_replacements} replacements")
            
            except Exception as e:
                print(f"Error processing {ml_file}: {e}")
        
        if files_changed_for_rule > 0:
            print(f"Rule: {old_pattern} → {new_pattern}")
            print(f"  Files modified: {files_changed_for_rule}, Total replacements: {replacements_for_rule}")
            stats['files_modified'] += files_changed_for_rule
            stats['total_replacements'] += replacements_for_rule
    
    # Count unique files processed
    stats['files_processed'] = len(ml_files)
    
    return stats


def main():
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Apply module type renamings from fixes.md'
    )
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Show what would be changed without actually modifying files'
    )
    parser.add_argument(
        '--fixes-file',
        default='fixes.md',
        help='Path to the fixes.md file (default: fixes.md)'
    )
    parser.add_argument(
        '--lib-dir',
        default='lib',
        help='Path to the lib directory (default: lib)'
    )
    
    args = parser.parse_args()
    
    # Resolve paths
    script_dir = Path(__file__).parent
    fixes_path = script_dir / args.fixes_file
    lib_dir = script_dir / args.lib_dir
    
    if not fixes_path.exists():
        print(f"Error: {fixes_path} not found")
        return 1
    
    if not lib_dir.exists() or not lib_dir.is_dir():
        print(f"Error: {lib_dir} is not a valid directory")
        return 1
    
    print(f"Parsing {fixes_path}...")
    rules = parse_fixes_file(fixes_path)
    print(f"Found {len(rules)} transformation rules\n")
    
    if args.dry_run:
        print("DRY RUN MODE - No files will be modified\n")
    
    print(f"Applying transformations to files in {lib_dir}...\n")
    stats = apply_replacements(lib_dir, rules, dry_run=args.dry_run)
    
    print("\n" + "="*60)
    print("Summary:")
    print(f"  Total .ml files scanned: {stats['files_processed']}")
    print(f"  Files with modifications: {stats['files_modified']}")
    print(f"  Total replacements made: {stats['total_replacements']}")
    
    if args.dry_run:
        print("\n(DRY RUN - no files were actually modified)")
    
    return 0


if __name__ == '__main__':
    exit(main())
