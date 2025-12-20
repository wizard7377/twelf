# SML to OCaml Converter - Quick Start

## 📁 Directory Structure

```
grep/sr/
├── 📄 README.md                    # Main documentation
├── 📄 INSTALL.md                   # Installation guide
├── 📄 QUICKSTART.md                # This quick reference guide
├── 📄 SML_TO_OCAML_CONVERTER.md   # Detailed converter documentation
├── 📄 INDEX.md                     # Project index
├── 📄 COMPLETION_SUMMARY.md        # Implementation summary
├── 📄 Pipfile                      # Python dependencies
│
├── 📂 src/                         # Core converter modules
│   ├── sml_process.py             # Main converter (790 lines)
│   ├── grammar.py                 # Grammar utilities
│   ├── grammar.js                 # Tree-sitter grammar
│   ├── main.py                    # Command-line interface
│   └── __init__.py
│
├── 📂 test_suite/                  # Test files
│   ├── test_converter.py          # Main test suite (50+ tests)
│   ├── test_ocaml.py              # OCaml validation tests
│   ├── test_corpus.py             # Corpus tests for SML sources
│   └── __init__.py
│
├── 📂 examples/                    # Example conversions
│   ├── examples.py                # Demo programs (15 examples)
│   ├── __init__.py
│   └── sml_sources/               # SML source files for testing
│       ├── compat/
│       ├── compile/
│       └── ...                    # Various SML modules
│
└── 📂 python/                      # Tree-sitter SML bindings
    └── tree_sitter_sml/
```

## ⚡ Quick Start

### 1. Install Dependencies

```bash
pip install tree-sitter tree-sitter-ocaml
```

Or using pipenv:
```bash
pipenv install
pipenv shell
```

See [INSTALL.md](INSTALL.md) for detailed installation instructions.

### 2. Run Examples

```bash
python examples/examples.py
```

### 3. Run Tests

```bash
# Run all tests
python -m unittest discover -s test_suite -p "test_*.py" -v

# Run specific test file
python -m unittest test_suite.test_converter -v
```

### 4. Convert SML Files

```bash
# Using the command-line interface
python src/main.py input.sml output.ml

# Using as a Python module
python -c "from src.sml_process import process_code; print(process_code('val x = 5'))"
```

## 📚 Documentation

- **[README.md](README.md)** - Main documentation with features, usage, and examples
- **[INSTALL.md](INSTALL.md)** - Complete installation guide
- **[SML_TO_OCAML_CONVERTER.md](SML_TO_OCAML_CONVERTER.md)** - Detailed converter documentation

## 🔑 Key Requirements

**Must be installed:**
- ✅ `tree-sitter` - Python bindings for tree-sitter
- ✅ `tree-sitter-ocaml` - OCaml language support

**Included in project:**
- ✅ `tree_sitter_sml` - Custom SML grammar bindings (in `python/` directory)

## 💡 Usage Examples

### Basic Conversion

```python
from src.sml_process import process_code

sml_code = """
fun factorial n =
  if n <= 1 then 1
  else n * factorial (n - 1)
"""

ocaml_code = process_code(sml_code)
print(ocaml_code)
```

### Batch Processing

```python
from pathlib import Path
from src.sml_process import process_code

# Convert all SML files in a directory
for sml_file in Path("examples/sml_sources/compat").glob("*.sml"):
    ocaml_file = sml_file.with_suffix(".ml")
    ocaml_code = process_code(sml_file.read_text())
    ocaml_file.write_text(ocaml_code)
```

## 🧪 Testing

```bash
# Run all tests with verbose output
python -m unittest discover -s test_suite -v

# Run with coverage
pip install coverage
coverage run -m unittest discover -s test_suite
coverage report
```

## 🤝 Contributing

See [README.md#Contributing](README.md#contributing) for information on extending the converter.

## 📝 License

See project documentation for licensing information.

---

**Need help?** Check [INSTALL.md](INSTALL.md) for troubleshooting or [README.md](README.md) for detailed usage.
