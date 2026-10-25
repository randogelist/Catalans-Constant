# Catalan’s Constant

**Conditional formal closure · Lean 4.33.0**

[![Lean CI](https://github.com/randogelist/Catalans-Constant/actions/workflows/lean.yml/badge.svg)](https://github.com/randogelist/Catalans-Constant/actions/workflows/lean.yml)

> **Main result**
>
> If finite integer-window certificates exist for every positive denominator scope, then Catalan’s constant is irrational.

Lean also proves that this **arithmetic exhaustion** condition is equivalent to the existence of a Catalan successor that preserves admission and doubles the scope.

**The universal existence condition remains open.** The formal closure is conditional on that premise.

### What is verified

| Result | Status |
| :--- | :--- |
| Conditional closure for the actual Catalan constant | Proved in Lean |
| Rational denominator exclusion through $10^{500}$ | Proved unconditionally |
| Universal arithmetic exhaustion | Open |

[**Exact statement**](docs/RESULT.md) · [**Lean proof**](CatalanAnchor/ArithmeticClosure.lean) · [**CI and axiom audit**](docs/VERIFICATION.md)
