# Exact conditional result

The namespace is `CatalanAnchor.RieszAdmission`. Put
`M = EulerUniform.workScale k`, `L = EulerUniform.lower k`, and
`U = EulerUniform.upper k`.

`IntegerWindow k B q d` is the conjunction

$$q>0,\quad d>0,\quad BM-qU>0,\quad BM-qL>0,\quad d(BM-qL)<M.$$

All quantities are integers. The finite recurrence uses
$M=10^{k+12}$ and $4(k+12)$ terms. The uniform analytic theorem proves
$L/M\le G\le U/M$ for every precision index $k$.

Consequently, `integerWindow_native_linear_form` proves

$$0<B-qG<1/d.$$

`ArithmeticExhaustion` asserts that such a window exists for **every** positive
scope $d$. Each instance is decidable; the universally quantified existence
statement has not been proved.

## Closure chain

| Lean declaration | Exact role |
| --- | --- |
| `CATALAN_NATIVE_IDENTIFIED` | Identifies the real part of the Mathlib Hurwitz-zeta construction with the convergent Catalan series. |
| `EulerUniform.scaled_enclosure` | Proves the enclosure for every precision index. |
| `seed_admissible` | Admits the saved finite coordinate for every proposed successor. |
| `linear_laws` | Proves the integer-linear-form interpretation for every admitted coordinate. |
| `successor_iff_arithmetic_exhaustion` | Equates successor existence with the universal integer-window existence premise. |
| `lock_iff_arithmetic_exhaustion` | Equates lock existence with that same premise. |
| `NATIVE_CATALAN_IRRATIONAL_OF_ARITHMETIC_EXHAUSTION` | Derives irrationality of the identified real constant from that premise. |

`successorOfCofinal` in `CatalanAnchor/CofinalClosure.lean` uses classical
choice to select admitted coordinates of sufficient scope. It is an existence
construction conditional on a cofinal family, not an executable search with
proved termination. The package does not claim an equivalence between
`ArithmeticExhaustion` and irrationality.

The terminology **conditional formal closure** refers to this proved reduction.
It does not assert that a single accepted finite witness discharges the universal
premise, and it is not an unconditional irrationality result.

## Finite result

`NATIVE_CATALAN_FINITE_SCOPE_10_POW_500` proves

$$\forall r\in\mathbb Q,\quad\operatorname{den}(r)\le10^{500}
\Longrightarrow (r:\mathbb R)\ne G.$$

`NATIVE_CATALAN_FINITE_SCOPE_1000` gives the stronger exact bound
`Certificate1000.bound`. The 1,000-place analytic enclosure, fixed-point
rounding, and concrete integer computation are all in the proof chain.
`seed_covers_finite_scopes` covers every positive scope through that finite bound.

The proved `identity_seed_checks` and `identity_not_lock` exhibit the distinction:
the same seed passes local admission for the identity successor, while that
successor cannot satisfy the lock laws.
