import argparse
from pathlib import Path
import sys

# Add parent directory and python bindings to path
ROOT_DIR = Path(__file__).resolve().parents[1]
PY_BINDINGS = ROOT_DIR / "python"
SRC_DIR = Path(__file__).resolve().parent

if str(PY_BINDINGS) not in sys.path:
    sys.path.append(str(PY_BINDINGS))
if str(SRC_DIR) not in sys.path:
    sys.path.append(str(SRC_DIR))

from sml_process import process_code


def main(args) -> None:
    parser = argparse.ArgumentParser(
        description="Process SML source code and write the converted output to a file.",
    )
    parser.add_argument("input_file", help="Path to the input SML source file")
    parser.add_argument("output_file", help="Path to write the processed output")
    args = parser.parse_args()
    print(args.input_file, args.output_file)
    input_text = Path(args.input_file).read_text(encoding="utf-8")
    output_text = process_code(input_text)
    Path(args.output_file).write_text(output_text, encoding="utf-8")

if __name__ == "__main__": 
    main(sys.argv)


