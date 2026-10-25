#!/usr/bin/env python3
"""Recover the saved finite Catalan witness using exact Python integers only.

The Euler enclosure's analytic justification is proved in the Lean sources.
This script independently replays its finite arithmetic and searches convergents
of the interval midpoint; it does not establish universal arithmetic exhaustion.
"""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def lean_integer(source, name):
    match = re.search(rf"^def {re.escape(name)} : [ℤℕ] := (-?\d+)\s*$", source, re.M)
    require(match is not None, f"missing literal Lean definition: {name}")
    return int(match.group(1))


def main():
    digits, guard = 1000, 12
    scale, factor = 10 ** digits, 10 ** guard
    work_scale, terms = scale * factor, 4 * (digits + guard)
    u = a = work_scale // 2
    total = 0
    for n in range(terms):
        next_u = (n + 1) * u // (2 * n + 3)
        next_a = ((n + 1) * a + next_u) // (2 * n + 3)
        total += a
        u, a = next_u, next_a
    require((u, a) == (0, 0), "unexpected terminal Euler state")
    require(work_scale < 2 ** terms, "Euler tail bound failed")
    upper = total + 3 * terms + 1
    lo, hi = total // factor, upper // factor + 1
    require(lo * factor < total and upper < hi * factor, "strict margins failed")
    require(hi == lo + 1, "Euler enclosure does not fit one decimal cell")

    # Standard continued fractions of the exact interval midpoint.
    num, den = lo + hi, 2 * scale
    p_prev, p = 0, 1
    q_prev, q = 1, 0
    tested = passing = records = 0
    best_scope, best = 0, None
    while den:
        quotient, remainder = divmod(num, den)
        pn, qn = quotient * p + p_prev, quotient * q + q_prev
        low, high = qn * lo - pn * scale, qn * hi - pn * scale
        A, B = qn, -pn
        if high < 0:
            low, high, A, B = -high, -low, -qn, pn
        if low > 0 and high > 0:
            scope = (scale - 1) // high
            if scope > 0:
                passing += 1
                if scope > best_scope:
                    best_scope, best = scope, (A, B, tested)
                    records += 1
        tested += 1
        p_prev, p, q_prev, q = p, pn, q, qn
        num, den = den, remainder
    require(best is not None, "no finite certificate recovered")
    A, B, index = best
    require((tested, passing, records, index) == (1896, 969, 968, 967),
            "continued-fraction search differs from the saved run")

    certificate = dict(line.split("=", 1) for line in
                       (ROOT / "examples/certificate_1000.txt").read_text().splitlines())
    require(certificate.get("FORMAT") == "CATALAN_SCOPE_CERTIFICATE_V1", "wrong format")
    recovered = {"SCALE_DIGITS": digits, "LOWER_INTEGER": lo, "UPPER_INTEGER": hi,
                 "A": A, "B": B, "DENOMINATOR_BOUND": best_scope}
    for name, value in recovered.items():
        require(int(certificate[name]) == value, f"saved certificate mismatch: {name}")
    lean = (ROOT / "CatalanAnchor/Certificate1000.lean").read_text()
    for name, value in {"lo": lo, "hi": hi, "A": A, "B": B, "bound": best_scope}.items():
        require(lean_integer(lean, name) == value, f"Lean certificate mismatch: {name}")
    computed = (ROOT / "CatalanAnchor/EulerComputed.lean").read_text()
    require(lean_integer(computed, "sumValue") == total, "Lean Euler sum mismatch")
    require(lean_integer(computed, "terms") == terms, "Lean Euler step-count mismatch")
    require(A < 0, "recovered best form has unexpected orientation")
    q = -A
    require(B * scale - q * hi > 0 and
            0 < best_scope * (B * scale - q * lo) < scale, "saved window failed")
    require(B * work_scale - q * upper > 0 and
            0 < best_scope * (B * work_scale - q * total) < work_scale,
            "uniform Euler window failed")
    require(10 ** 500 <= best_scope < 10 ** 501, "unexpected denominator scope")
    print("EULER_INTEGER_REPLAY=PASS\nCERTIFICATE_RECONSTRUCTED=PASS\nLEAN_DATA_MATCH=PASS")
    print(f"CANDIDATES={tested} PASSING={passing} RECORDS={records} CF_INDEX={index}")
    print("FINITE_DENOMINATOR_SCOPE=PASS\nBOUND_DECIMAL_DIGITS=501\nSCOPE_AT_LEAST=10^500")
    print("ARITHMETIC_EXHAUSTION=NOT_PROVED\nLEAN_COMPILATION=NOT_PERFORMED")


if __name__ == "__main__":
    try:
        main()
    except (OSError, UnicodeError, ValueError, KeyError) as exc:
        print(f"RECONSTRUCTION=FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
