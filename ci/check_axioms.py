#!/usr/bin/env python3
"""Require every declared audit record and enforce the standard-axiom allowlist."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

from check_sources import strip_comments_and_strings


ALLOWLIST = frozenset({"propext", "Classical.choice", "Quot.sound"})
EXPECTED_DECLARATIONS = 88
NAME = r"[A-Za-z_][A-Za-z_0-9'.]*"
DIRECTIVE = re.compile(rf"^\s*#print\s+axioms\s+({NAME})\s*$", re.MULTILINE)
RECORD = re.compile(
    r"^[ \t]*'(?P<name>[^'\r\n]+)'[ \t]+(?:"
    r"depends on axioms:[ \t]*\[(?P<axioms>[^\[\]]*)\]|"
    r"does not depend on any axioms)[ \t]*$",
    re.MULTILINE,
)


class AuditError(ValueError):
    pass


def expected_names(source: str) -> tuple[str, ...]:
    code = strip_comments_and_strings(source)
    names = tuple(DIRECTIVE.findall(code))
    directive_count = len(re.findall(r"#print\s+axioms\b", code))
    if directive_count != len(names):
        raise AuditError("malformed #print axioms directive in audit source")
    if len(names) != len(set(names)):
        raise AuditError("duplicate #print axioms declaration in audit source")
    if len(names) != EXPECTED_DECLARATIONS:
        raise AuditError(
            f"expected {EXPECTED_DECLARATIONS} audit declarations, found {len(names)}"
        )
    return names


def verify_log(log: str, expected: tuple[str, ...]) -> dict[str, frozenset[str]]:
    log = log.replace("\r\n", "\n")
    if re.search(r"\berror:", log, re.IGNORECASE):
        raise AuditError("Lean error diagnostic present in audit log")
    records: dict[str, frozenset[str]] = {}
    spans = []
    for match in RECORD.finditer(log):
        spans.append(match.span())
        name = match.group("name")
        if not re.fullmatch(NAME, name):
            raise AuditError(f"malformed audited declaration name: {name!r}")
        if name in records:
            raise AuditError(f"duplicate audit record: {name}")
        value = match.group("axioms")
        raw = [] if value is None or not value.strip() else value.split(",")
        axioms = [item.strip() for item in raw]
        if any(not re.fullmatch(NAME, item) for item in axioms):
            raise AuditError(f"malformed axiom list for {name}")
        if len(set(axioms)) != len(axioms):
            raise AuditError(f"duplicate axiom in list for {name}")
        forbidden = set(axioms) - ALLOWLIST
        if forbidden:
            raise AuditError(f"forbidden axiom for {name}: {', '.join(sorted(forbidden))}")
        records[name] = frozenset(axioms)

    # Any leftover audit-like record is malformed, rather than silently ignored.
    remaining = list(log)
    for start, end in spans:
        remaining[start:end] = " " * (end - start)
    residue = "".join(remaining)
    if re.search(r"depends on axioms|does not depend on any axioms", residue):
        raise AuditError("malformed axiom audit record")
    missing = set(expected) - records.keys()
    extra = records.keys() - set(expected)
    if missing or extra:
        details = []
        if missing:
            details.append("missing: " + ", ".join(sorted(missing)))
        if extra:
            details.append("unexpected: " + ", ".join(sorted(extra)))
        raise AuditError("; ".join(details))
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--source", type=Path, default=Path("CatalanAnchor/Audit.lean"))
    args = parser.parse_args()
    try:
        expected = expected_names(args.source.read_text(encoding="utf-8"))
        records = verify_log(args.log.read_text(encoding="utf-8"), expected)
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"AXIOM_AUDIT=FAIL\n{exc}", file=sys.stderr)
        return 1
    print(f"AXIOM_AUDIT=PASS\nAUDITED_DECLARATIONS={len(records)}")
    print("AXIOM_ALLOWLIST=" + ",".join(sorted(ALLOWLIST)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
