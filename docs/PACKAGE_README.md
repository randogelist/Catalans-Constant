# CATALAN_CLOSURE_REDUCTION_v0_2_0

Lean 4.33.0. This package extends CATALAN_RIESZ_ADMISSION_v0_1_0 with an exact equivalence for the remaining existence obligation.

## Checked closure statement

In namespace `CatalanAnchor.RieszAdmission`:

```lean
theorem successor_iff_arithmetic_exhaustion :
  Nonempty CatalanSuccessor ↔ ArithmeticExhaustion

theorem NATIVE_CATALAN_IRRATIONAL_OF_ARITHMETIC_EXHAUSTION
  (h : ArithmeticExhaustion) : Irrational nativeCatalan
```

`ArithmeticExhaustion` means

```lean
∀ d : ℕ, 0 < d → ∃ k : ℕ, ∃ B : ℤ, ∃ q : ℕ,
  IntegerWindow k B q d
```

For `M = EulerUniform.workScale k`, `L = EulerUniform.lower k`, and `U = EulerUniform.upper k`, the decidable integer condition is

```text
q > 0, d > 0,
B*M - q*U > 0,
B*M - q*L > 0,
d*(B*M - q*L) < M.
```

These are finite integer computations. Here `M = 10^(k+12)`, the Euler recurrence has `4*(k+12)` terms, and `U = L + 3*terms + 1`. The analytic enclosure of the actual Catalan constant is proved for every k in the inherited sources.

Every accepted window gives the proved native statement

```text
0 < B - q*nativeCatalan < 1/d.
```

The equivalence chain is:

```text
Nonempty CatalanSuccessor
  iff existence of next with LockLaws (system next)
  iff CofinalAdmission
  iff CofinalCheckedAdmission
  iff ArithmeticExhaustion.
```

All these conditions imply irrationality of the identified real Catalan constant. The package does not prove these existence conditions unconditionally. It does not assert the reverse implication from irrationality.

## What is new

- `CatalanAnchor/CofinalClosure.lean`: cofinal finite admissions are equivalent to successor existence and lock existence. Classical choice constructs a successor from the assumed cofinal family.
- `CatalanAnchor/ArithmeticClosure.lean`: replaces coordinate language with the explicit integer window above, proves equivalence, native soundness, and the conditional endpoint.
- `seed_covers_finite_scopes`: the existing seed supplies every positive scope d through `Certificate1000.bound`, including all d through `10^500`.

Classical selection is not an algorithmic witness search or a proof that a search terminates. The universal quantifier over d remains the exact unproved premise. Increasing a finite precision or checking another finite witness does not discharge it.

## Preserved results

The package retains the series/Hurwitz-zeta identification of `nativeCatalan`, analytic Euler enclosure, fixed-point rounding proof, 1,000-place integer interval replay, unconditional 501-digit finite denominator exclusion, admitted seed, universal linear laws, and bounded-precision and identity-successor obstructions.

The endpoint refers to the actual real Catalan constant through the proved `CATALAN_NATIVE_IDENTIFIED` theorem. There is no unproved Catalan-identification or analytic-bridge argument in this closure chain.

## Run on native Windows

From Downloads:

```cmd
cd /d "%USERPROFILE%\Downloads" && tar -xf "CATALAN_CLOSURE_REDUCTION_v0_2_0.zip" && call "CATALAN_CLOSURE_REDUCTION_v0_2_0\run.cmd"
```

Uses the same existing native Lean 4.33.0 and Mathlib cache as the preceding package. No network, Lake, Python, PowerShell, or WSL is used by `run.cmd`.

Optional environment overrides:

```cmd
set "CATALAN_LEAN_EXE=C:\path\to\lean.exe"
set "CATALAN_CACHE_ROOT=C:\path\to\existing\mathlib-project"
set "CATALAN_LEAN_THREADS=2"
```

The earlier `ZETA3_LEAN_EXE` and `ZETA3_CACHE_ROOT` overrides remain supported. Build output goes to `build`; logs go to `logs`.

## Trust and limits

Sources use no unproved declarations, placeholders, or native Boolean oracle. The checked declaration audit lists only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. See `VALIDATION.txt` and `AXIOM_AUDIT.txt` for this version's checks.

```text
EXACT_CLOSURE_REDUCTION=PROVED
ARITHMETIC_EXHAUSTION=NOT_PROVED
RIESZ_LOCK=NOT_CONSTRUCTED
UNCONDITIONAL_CATALAN_IRRATIONALITY=NOT_CLAIMED
```
