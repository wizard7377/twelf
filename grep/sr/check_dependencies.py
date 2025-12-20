#!/usr/bin/env python3
"""
Verification script to check if all required dependencies are available.
Run this before using the SML to OCaml converter.
"""

import sys
from pathlib import Path

def check_dependency(name, import_name=None):
    """Check if a dependency is available."""
    if import_name is None:
        import_name = name.replace('-', '_')
    
    try:
        __import__(import_name)
        print(f"✅ {name}: INSTALLED")
        return True
    except ImportError:
        print(f"❌ {name}: NOT INSTALLED")
        return False

def main():
    print("=" * 60)
    print("SML to OCaml Converter - Dependency Check")
    print("=" * 60)
    print()
    
    # Check required dependencies
    print("Required Dependencies:")
    print("-" * 60)
    
    tree_sitter_ok = check_dependency("tree-sitter", "tree_sitter")
    tree_sitter_ocaml_ok = check_dependency("tree-sitter-ocaml", "tree_sitter_ocaml")
    
    print()
    print("Included Dependencies:")
    print("-" * 60)
    
    # Check tree-sitter-sml (should be in python/ directory)
    sml_bindings_path = Path(__file__).parent / "python" / "tree_sitter_sml"
    if sml_bindings_path.exists():
        sys.path.insert(0, str(Path(__file__).parent / "python"))
        tree_sitter_sml_ok = check_dependency("tree-sitter-sml", "tree_sitter_sml")
        if tree_sitter_sml_ok:
            print(f"   Location: {sml_bindings_path}")
    else:
        print(f"❌ tree-sitter-sml: NOT FOUND at {sml_bindings_path}")
        tree_sitter_sml_ok = False
    
    print()
    print("=" * 60)
    print("Summary:")
    print("=" * 60)
    
    all_ok = tree_sitter_ok and tree_sitter_ocaml_ok and tree_sitter_sml_ok
    
    if all_ok:
        print("✅ All dependencies are available!")
        print()
        print("You can now use the converter:")
        print("  python examples/examples.py")
        print("  python src/main.py input.sml output.ml")
        print("  python -m unittest discover -s test_suite")
        return 0
    else:
        print("❌ Some dependencies are missing.")
        print()
        print("To install missing dependencies:")
        if not tree_sitter_ok:
            print("  pip install tree-sitter")
        if not tree_sitter_ocaml_ok:
            print("  pip install tree-sitter-ocaml")
        if not tree_sitter_sml_ok:
            print("  ERROR: tree-sitter-sml bindings are missing from python/tree_sitter_sml/")
            print("         Please ensure the directory structure is intact.")
        print()
        print("See INSTALL.md for detailed installation instructions.")
        return 1

if __name__ == "__main__":
    sys.exit(main())
