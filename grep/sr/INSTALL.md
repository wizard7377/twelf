# Installation Guide

## Required Dependencies

Before using the SML to OCaml converter, you must install the following dependencies:

### 1. tree-sitter

Tree-sitter is required for parsing code.

```bash
pip install tree-sitter
```

### 2. tree-sitter-ocaml

OCaml language support for tree-sitter is needed for OCaml code generation.

```bash
pip install tree-sitter-ocaml
```

### 3. tree-sitter-sml (Included)

**Good news!** The SML grammar bindings for tree-sitter are already included in the project at `python/tree_sitter_sml/`. You don't need to install anything extra for SML parsing.

The converter scripts automatically add this directory to the Python path, so the bindings are available without additional installation.

## Installation Methods

### Method 1: Using pip (Recommended)

Install the required packages directly:

```bash
pip install tree-sitter tree-sitter-ocaml
```

### Method 2: Using pipenv

If you prefer using pipenv for virtual environment management:

```bash
# Install pipenv if you don't have it
pip install pipenv

# Navigate to the project directory
cd /path/to/grep/sr

# Install all dependencies from Pipfile
pipenv install

# Activate the virtual environment
pipenv shell
```

### Method 3: Using requirements.txt

If you prefer a requirements file:

```bash
# Create requirements.txt (already done if you have Pipfile)
pip install -r requirements.txt
```

Contents of `requirements.txt`:
```
tree-sitter
tree-sitter-ocaml
```

## Verification

After installation, verify that all dependencies are available:

```bash
# Run the dependency checker (recommended)
python check_dependencies.py
```

Or check manually:

```bash
# Check tree-sitter installation
python -c "import tree_sitter; print(f'tree-sitter version: {tree_sitter.__version__}')"

# Check tree-sitter-ocaml installation
python -c "import tree_sitter_ocaml; print('tree-sitter-ocaml installed successfully')"

# Check tree-sitter-sml (included)
python -c "import sys; sys.path.append('python'); import tree_sitter_sml; print('tree-sitter-sml available')"
```

## Python Version Requirements

- **Python 3.7 or higher** is required
- The project is tested with Python 3.13 (as specified in Pipfile)

## Troubleshooting

### ImportError: No module named 'tree_sitter'

**Solution**: Install tree-sitter:
```bash
pip install tree-sitter
```

### ImportError: No module named 'tree_sitter_ocaml'

**Solution**: Install tree-sitter-ocaml:
```bash
pip install tree-sitter-ocaml
```

### ImportError: No module named 'tree_sitter_sml'

**Solution**: The SML grammar bindings are included in the project at `python/tree_sitter_sml/`. This error usually means:

1. The `python/tree_sitter_sml/` directory is missing or corrupted
2. You're running the script from an unexpected location

**Fix**: Ensure you're running scripts from the `grep/sr/` directory, or the directory structure is intact:
```bash
cd /path/to/grep/sr
ls python/tree_sitter_sml/  # Should show __init__.py, binding.c, etc.
```

The converter automatically adds the `python/` directory to the Python path, so no manual installation is needed.

### Permission Denied Errors

**Solution**: Use a virtual environment or install with user flag:
```bash
pip install --user tree-sitter tree-sitter-ocaml
```

### Version Conflicts

**Solution**: Use a virtual environment:
```bash
python -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate
pip install tree-sitter tree-sitter-ocaml
```

## Running the Converter

After installation, you can run the converter:

```bash
# From the grep/sr directory

# Run examples
python examples/examples.py

# Run tests
python -m unittest discover -s test_suite -p "test_*.py"

# Use the command-line interface
python src/main.py input.sml output.ml
```

## Development Setup

For development work, you may want to install additional packages:

```bash
# Install coverage for test coverage reports
pip install coverage

# Run tests with coverage
coverage run -m unittest discover -s test_suite
coverage report
coverage html  # Generate HTML report
```

## Additional Resources

- [tree-sitter Documentation](https://tree-sitter.github.io/tree-sitter/)
- [tree-sitter Python Bindings](https://github.com/tree-sitter/py-tree-sitter)
- [OCaml Official Website](https://ocaml.org/)
- [SML/NJ Documentation](https://www.smlnj.org/)
