import argparse
from pathlib import Path
import sys

try:
    from grep.sr.sml_process import process_code
except ModuleNotFoundError:
    sys.path.append(str(Path(__file__).resolve().parent))
    from sml_process import process_code


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Process SML source code and write the converted output to a file.",
    )
    parser.add_argument("input_file", help="Path to the input SML source file")
    parser.add_argument("output_file", help="Path to write the processed output")
    args = parser.parse_args()

    input_text = Path(args.input_file).read_text(encoding="utf-8")
    output_text = process_code(input_text)
    Path(args.output_file).write_text(output_text, encoding="utf-8")


if __name__ == "__main__":
    main()

