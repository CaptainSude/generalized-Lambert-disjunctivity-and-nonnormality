# Digits of power Lambert series

[Read the paper](paper/power-lambert-digits.pdf) · [LaTeX source](paper/power-lambert-digits.tex) · [Lean proof](lean/PowerLambert/Results.lean)

For every pair of integers $b,r\ge2$, let

$$
L_{b,r}=\sum_{m=1}^{\infty}\frac{1}{b^{m^r}-1}.
$$

Every finite word in the base-$b$ expansion of $L_{b,r}$ has a strictly positive limiting frequency, but $L_{b,r}$ is not normal in base $b$. In particular, it is disjunctive and irrational. Occurrences may overlap, and the frequencies converge along all initial segments.

The radix orbit also has an explicit limiting probability law. This law is invariant and ergodic under multiplication by $b$ modulo $1$, has no atoms, has full support, and has zero Kolmogorov–Sinai entropy.

## Read the argument

The six-page paper explains how congruences force any prescribed word, how periodic approximation gives its limiting frequency, and why the limiting law has zero entropy and the number is not normal. References appear where their methods are used.

The paper has no author line. Mathematical sources and third-party code contributors are credited in the paper and [source provenance](lean/PROVENANCE.md).

## Check the proof

The main theorem is `PowerLambert.powerLambert_full_theorem` in [Results.lean](lean/PowerLambert/Results.lean). Its only hypotheses are `2 ≤ b` and `2 ≤ r`.

After installing [Lean through elan](https://github.com/leanprover/elan), open a terminal at the repository root and run:

```text
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

The toolchain and dependencies are pinned. [The verification record](lean/VERIFICATION.md) documents the successful clean build and axiom audit. The sources contain no unfinished proofs or additional axioms. The final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The **Lean verification** workflow runs the build and guarded axiom audit on pushes and pull requests. Its results appear in the repository's **Actions** tab.

See [the Lean README](lean/README.md) for a map of the formalization, or [the paper README](paper/README.md) to rebuild the PDF.

## Licenses

The paper is licensed under **CC BY 4.0**. The Lean code is licensed under **Apache 2.0**, with third-party notices retained. See [LICENSES.md](LICENSES.md).
