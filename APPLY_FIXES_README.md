# Module Type Renaming Scripts

These scripts automatically apply all the module type renamings described in `fixes.md`.

## Available Scripts

### Python Script (Recommended)

**File:** `apply_fixes.py`

**Usage:**
```bash
# Apply all changes
./apply_fixes.py

# Dry run (show what would change without modifying files)
./apply_fixes.py --dry-run

# Specify custom paths
./apply_fixes.py --fixes-file fixes.md --lib-dir lib
```

**Requirements:** Python 3.6+

**Features:**
- Uses regex word boundaries to ensure accurate matching
- Provides detailed output showing which files were modified
- Supports dry-run mode for testing
- Handles encoding properly

### Bash Script (Alternative)

**File:** `apply_fixes.sh`

**Usage:**
```bash
# Apply all changes
./apply_fixes.sh

# Dry run (show what would change without modifying files)
./apply_fixes.sh --dry-run
```

**Requirements:** bash, sed, grep, find

**Features:**
- Simple bash implementation
- Uses word boundaries for accurate matching
- Supports dry-run mode

## What the Scripts Do

The scripts parse `fixes.md` and for each rule:

1. Extract the excluded file, old pattern, and new pattern
2. Find all `.ml` files in the `lib/` directory
3. Skip the excluded file for that rule
4. Replace all occurrences of the old pattern with the new pattern (using word boundaries)
5. Report statistics on files modified and replacements made

## Example Output

```
Parsing fixes.md...
Found 203 transformation rules

Applying transformations to files in lib...

Rule: COMPAT_ARRAY → Array.COMPAT_ARRAY
  compat/compat.ml: 2 replacements
  Files modified: 1, Total replacements: 2

Rule: ARRAY_SLICE → Array_slice.ARRAY_SLICE
  (no files modified)

...

========================================
Summary:
  Total .ml files scanned: 450
  Files with modifications: 125
  Total replacements made: 487
```

## Safety Features

- **Word boundary matching**: Only replaces whole words, not partial matches
- **File exclusion**: Each rule excludes its defining file from changes
- **Dry-run mode**: Test the changes before applying them
- **Error handling**: Continues processing even if individual files fail

## Recommended Workflow

1. **Always run dry-run first:**
   ```bash
   ./apply_fixes.py --dry-run
   ```

2. **Review the output** to ensure changes look correct

3. **Apply the changes:**
   ```bash
   ./apply_fixes.py
   ```

4. **Test the build** to ensure no regressions

5. **Commit the changes** with version control

## Notes

- Both scripts use word boundary matching to avoid partial replacements
- The Python script is generally more robust and provides better error handling
- Make sure to have backups or use version control before running
- Some rules may not result in any changes if the pattern doesn't exist in other files
