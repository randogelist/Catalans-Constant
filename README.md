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

### Verified finite witness

The saved seed is admitted by the finite checker:

```math
\large
\pmb{
\begin{gathered}
W_0=(1000,B_0,q_0,D_0),\\[4pt]
\mathrm{IntegerWindow}(1000,B_0,q_0,D_0),\\[4pt]
0 \lt B_0-q_0G \lt \frac{1}{D_0},
\qquad D_0 \gt 10^{500}.
\end{gathered}
}
```

Here $`D_0\approx1.0203550081346944\times10^{500}`$. This witness certifies every positive scope $`d\le D_0`$; the universal continuation remains the open premise above.

[**Exact certificate**](examples/certificate_1000.txt) · [**Lean admission proof**](CatalanAnchor/Admission.lean) · [**Reconstruct the witness**](examples/reconstruct_witness.py)

<details>
<summary>Exact witness integers</summary>

Concatenate the rows within each block to obtain the exact integer; no digits are omitted. In the saved certificate, these are `B`, `-A`, and `DENOMINATOR_BOUND`, respectively.

**B₀**

```text
22478589411709532859520719051824040739769231852523
58308204514785180195540158471631488901762306492837
95184165871753406826993624725913103859973600980421
95954860016519274721183642305796663919612196551006
85118423851934201891996221141422973373713476751034
17407600400665530955502039527496243372408487943932
74344652366991938975735409225492806939697551451966
80504568060408371861591081088994168764436911993885
95545264498464073978792018709865908707052196658591
42234364374246496189298228725320519373359695418674
```

**q₀**

```text
24540866550671361418870363398507305828437681675338
76161164598787271227033584214540635579996707584555
65728097279854831107342338652043133067750793159294
19585212748689465220458097287970758116602564491079
57998885786551382973814586691526278932134438381299
73051216867301499840539966559705581159942661064028
42850678335118528256765370251366990877801465544545
42200737346508594309332502957498817930877244298876
02560523459723575426057093408325128848513516742831
93257873678400456946962185654569033760321060980349
```

**D₀**

```text
10203550081346944200260438208511353464501456253918
51811043470440511830140566974389733127184106068441
22805260968277046387965061883585943441532591575817
96933456606677640226845238010367269611648714177827
02609285664931393294620991603636783473656325127311
77378690070326997098676309365193488476365386078923
51923709787898740984265652450869407886139552204898
76339887083794801804766808830182257484313088415852
81021642344513098558790732928034446828376882415984
04114554614712449309589387202386077164328280337110
3
```

The reconstruction replays all 4,048 integer Euler steps and recovers $`B_0/q_0`$ as the 968th regular continued-fraction convergent of the midpoint of the proved 1,000-place enclosure. It reproduces the saved scope and checks all strict integer margins.

```sh
python3 examples/reconstruct_witness.py
```

</details>

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
