# Catalan’s constant — conditional formal closure

[![Lean CI](https://github.com/randogelist/Catalans-Constant/actions/workflows/lean.yml/badge.svg)](https://github.com/randogelist/Catalans-Constant/actions/workflows/lean.yml)

For the actual Catalan constant

$$G=\sum_{n=0}^{\infty}\frac{(-1)^n}{(2n+1)^2},$$

the main result is the conditional formal closure:

$$\boxed{\operatorname{Nonempty}(\mathrm{CatalanSuccessor})
\iff \mathrm{ArithmeticExhaustion}},$$

$$\boxed{\mathrm{ArithmeticExhaustion}\Longrightarrow G\notin\mathbb Q}.$$

Here **ArithmeticExhaustion** is the explicit premise

$$\forall d\in\mathbb N_{>0},\ \exists k\in\mathbb N,\ B\in\mathbb Z,\ q\in\mathbb N,
\quad\mathrm{IntegerWindow}(k,B,q,d).$$

Each window is a finite integer check proving $0<B-qG<1/d$.
A `CatalanSuccessor` preserves admission and at least doubles the denominator scope.
**The universal existence premise remains unproved; unconditional Catalan irrationality is not claimed.**

The exact Lean endpoints, in `CatalanAnchor.RieszAdmission`, are:

```lean
theorem successor_iff_arithmetic_exhaustion :
    Nonempty CatalanSuccessor ↔ ArithmeticExhaustion

theorem NATIVE_CATALAN_IRRATIONAL_OF_ARITHMETIC_EXHAUSTION
    (h : ArithmeticExhaustion) : Irrational nativeCatalan
```

[Main proof](CatalanAnchor/ArithmeticClosure.lean) · [Constant identification](CatalanAnchor/HurwitzBridge.lean) · [Precise premise and proof chain](docs/RESULT.md)

**Unconditional finite result:** every rational with reduced denominator at most $10^{500}$ differs from $G$. The saved certificate proves a stronger exact 501-digit bound; it does not discharge arithmetic exhaustion.

Lean **4.33.0** and Mathlib are pinned. [GitHub Actions](https://github.com/randogelist/Catalans-Constant/actions/workflows/lean.yml) builds the 24 project modules and checks all 88 listed declarations against the axiom allowlist `propext`, `Classical.choice`, `Quot.sound`. The badge and run logs report current CI status. [Verification and provenance](docs/VERIFICATION.md).
