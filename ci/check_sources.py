#!/usr/bin/env python3
"""Supplementary source trust scan; compiled axiom auditing is authoritative."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys


class SourceError(ValueError):
    pass


FORBIDDEN = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|constant|native_decide|unsafe|"
    r"ofReduceBool|ofReduceNat|trustCompiler)\b"
)
IGNORED_DIRS = {".lake", ".git", "build", "logs", "__pycache__"}


def strip_comments_and_strings(source: str) -> str:
    """Blank Lean comments and strings, retaining offsets and line numbers.

    Lean block comments nest. Comment delimiters in strings and string delimiters
    in comments must not change the surrounding state. This is a conservative
    source scan, not an alternative Lean parser or proof checker.
    """
    out = list(source)
    i = 0
    depth = 0
    in_string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif in_string:
            if source[i] == "\\":
                out[i] = " "
                i += 1
                if i < len(source):
                    if source[i] != "\n":
                        out[i] = " "
                    i += 1
            else:
                if source[i] == '"':
                    in_string = False
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end < 0:
                end = len(source)
            out[i:end] = " " * (end - i)
            i = end
        elif source.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif source[i] == '"':
            out[i] = " "
            in_string = True
            i += 1
        else:
            i += 1
    if depth or in_string:
        raise SourceError("unterminated block comment or string")
    return "".join(out)


def scan_text(source: str, label: str = "<source>") -> None:
    code = strip_comments_and_strings(source)
    match = FORBIDDEN.search(code)
    if match:
        line = code.count("\n", 0, match.start()) + 1
        raise SourceError(f"{label}:{line}: forbidden token {match.group()}")


def scan_tree(root: Path) -> int:
    files = sorted(
        path for path in root.rglob("*.lean")
        if not (set(path.relative_to(root).parts[:-1]) & IGNORED_DIRS)
    )
    if not files:
        raise SourceError("no project Lean source files found")
    for path in files:
        scan_text(path.read_text(encoding="utf-8"), str(path.relative_to(root)))
    return len(files)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, nargs="?", default=Path("."))
    args = parser.parse_args()
    try:
        count = scan_tree(args.root.resolve())
    except (OSError, UnicodeError, SourceError) as exc:
        print(f"SOURCE_TRUST_SCAN=FAIL\n{exc}", file=sys.stderr)
        return 1
    print(f"SOURCE_TRUST_SCAN=PASS\nSCANNED_LEAN_FILES={count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
