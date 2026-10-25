# Catalan’s Constant

[![Lean CI](https://github.com/randogelist/Catalans-Constant/actions/workflows/lean.yml/badge.svg)](https://github.com/randogelist/Catalans-Constant/actions/workflows/lean.yml)

## Main result

The theorem and its successor equivalence are proved in Lean for the actual Catalan constant:

> [!IMPORTANT]
> **Conditional formal closure on $`G\notin\mathbb{Q}`$.**
>
> ```math
> \large
> \pmb{
> \begin{gathered}
> \mathrm{Nonempty}(\mathrm{CatalanSuccessor})
> \;\Longleftrightarrow\;
> \mathcal{E}_G
> \\[6pt]
> \mathcal{E}_G
> \;\Longrightarrow\;
> G\notin\mathbb{Q}
> \end{gathered}
> }
> ```

Here $`\mathcal{E}_G`$ denotes **arithmetic exhaustion**, with the exact premise

```math
\large
\pmb{
\begin{aligned}
\mathcal{E}_G \;:\Longleftrightarrow\;&
\forall d\in\mathbb{N}_{>0},\\
&\exists k\in\mathbb{N},\ B\in\mathbb{Z},\ q\in\mathbb{N}_{>0}:\\
&\mathrm{IntegerWindow}(k,B,q,d).
\end{aligned}
}
```

Every positive scope must admit a finite certificate. The equivalent successor preserves admission and at least doubles the scope.

**The universal existence premise remains open.** The conditional theorem and the identification of the actual constant are proved; unconditional irrationality is not claimed.

[**Exact theorem**](docs/RESULT.md) · [**Lean proof**](CatalanAnchor/ArithmeticClosure.lean) · [**CI and axiom audit**](docs/VERIFICATION.md)

## Eight identifications of $`G`$

Catalan’s constant has the following equivalent representations.

| Form | Identity |
| :--- | :--- |
| Alternating series | $`\large\pmb{\displaystyle G=\sum_{n=0}^{\infty}\frac{(-1)^n}{(2n+1)^2}}`$ |
| Dirichlet beta | $`\large\pmb{\displaystyle G=\beta(2)}`$ |
| Hurwitz zeta | $`\large\pmb{\displaystyle G=\frac{\zeta(2,\frac{1}{4})-\zeta(2,\frac{3}{4})}{16}}`$ |
| Trigamma | $`\large\pmb{\displaystyle G=\frac{\psi_1(\frac{1}{4})-\psi_1(\frac{3}{4})}{16}}`$ |
| Inverse tangent integral | $`\large\pmb{\displaystyle G=\int_0^1\frac{\arctan t}{t}\,dt}`$ |
| Logarithmic integral | $`\large\pmb{\displaystyle G=-\int_0^1\frac{\log t}{1+t^2}\,dt}`$ |
| Trigonometric integral | $`\large\pmb{\displaystyle G=-\int_0^{\pi/4}\log(\tan t)\,dt}`$ |
| Unit-square integral | $`\large\pmb{\displaystyle G=\int_0^1\int_0^1\frac{1}{1+x^2y^2}\,dy\,dx}`$ |

Here $`\beta`$ is the Dirichlet beta function, $`\zeta(s,a)`$ the Hurwitz zeta function, and $`\psi_1`$ the trigamma function. The arctangent integrand has continuous value $`1`$ at zero; the logarithmic integrals are convergent improper integrals.

The **series, Hurwitz-zeta, and unit-square identifications are formalized in this repository**. The other identities give classical context; references appear below.

## Approach

The proved Euler recurrence encloses the actual constant between rational bounds. The finite checker has the following proved guarantee for $`B\in\mathbb{Z}`$ and $`q,d\in\mathbb{N}_{>0}`$:

```math
\large
\pmb{
\mathrm{IntegerWindow}(k,B,q,d)
\quad\Longrightarrow\quad
0 \lt B-qG \lt \frac{1}{d}.
}
```

A successor that preserves admission and at least doubles $`d`$ produces arbitrarily small positive integer linear forms. If $`G=a/b`$ were rational with $`b>0`$, multiplying these forms by $`b`$ would eventually give a positive integer smaller than $`1`$.

## Verified finite result

The saved certificate proves the unconditional finite exclusion:

```math
\large
\pmb{
\boxed{
\forall r\in\mathbb{Q},\qquad
\mathrm{den}(r)\le 10^{500}
\;\Longrightarrow\;
r\ne G
}
}
```

Lean 4.33.0 · pinned Mathlib · 24 Lean files · 88 audited declarations.

<details>
<summary>Identity references</summary>

- [NIST DLMF: Hurwitz-zeta series](https://dlmf.nist.gov/25.11.E1) and [Dirichlet L-series](https://dlmf.nist.gov/25.15.E1). Splitting the Catalan series into the two odd residue classes gives the Hurwitz identity; $`\beta(s)=L(s,\chi_4)`$.
- [NIST: trigamma series](https://www.itl.nist.gov/div898/software/dataplot/refman2/auxillar/trigamma.htm), giving $`\psi_1(a)=\zeta(2,a)`$ for $`a>0`$.
- [Inverse tangent integral, equations (1)–(2)](https://arxiv.org/html/2605.01830v1#S1). Integration by parts gives the logarithmic integral, and $`t=\tan\theta`$ gives the trigonometric integral.
- Repository proofs: [series](CatalanAnchor/Series.lean), [Hurwitz identification](CatalanAnchor/HurwitzBridge.lean), and [unit-square integral](CatalanAnchor/Integral.lean).

</details>
