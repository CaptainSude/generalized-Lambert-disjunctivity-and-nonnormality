# Power-exponent Lambert sums

Lean verification of the theorem for

\[
L_{b,r}=\sum_{m\ge1}\frac1{b^{m^r}-1},\qquad b,r\in\mathbb N,\quad b,r\ge2.
\]

Every finite word in the base-\(b\) expansion has a strictly positive limiting frequency. In particular, these constants are disjunctive and irrational, although they are not normal in base \(b\). Their radix-orbit empirical measures converge to an explicit invariant, ergodic, atomless probability measure with full support and zero Kolmogorov–Sinai entropy.

The complete statement is `PowerLambert.powerLambert_full_theorem` in [PowerLambert/Results.lean](PowerLambert/Results.lean). Its only hypotheses are the two integer inequalities `2 ≤ b` and `2 ≤ r`.

## Check the proof

Install [Lean using elan](https://github.com/leanprover/elan), open a terminal in this folder, and run:

```text
lake exe cache get
lake build
lake env lean Audit.lean
```

The toolchain and all external dependencies are pinned by `lean-toolchain` and `lake-manifest.json`. The first command downloads cached Mathlib proofs; the build checks the formalization. `Audit.lean` checks that the final theorems depend only on Lean's standard classical foundations: `propext`, `Classical.choice`, and `Quot.sound`.

The sources contain no `sorry`, unproved axioms, `admit`, or `native_decide`. No arithmetic, statistical, genericity, or entropy conclusion is supplied as an assumption to the final theorem.

## Read the formalization

| Topic | Source |
|---|---|
| Radix cylinders, overlapping frequencies, normality and disjunctivity | [Basic.lean](PowerLambert/Basic.lean) |
| Infinite Lambert sum and exact coefficient/carry bridge | [Series.lean](PowerLambert/Series.lean), [SeriesBridge.lean](PowerLambert/SeriesBridge.lean) |
| Prime valuations, CRT progression and coprime retained cofactor | [ArithmeticControlsConstruction.lean](PowerLambert/ArithmeticControlsConstruction.lean) |
| Power-free progression density | [PowerFreeSieve.lean](PowerLambert/PowerFreeSieve.lean) |
| Complete progression means and carry-tail estimates | [SeriesMeansTail.lean](PowerLambert/SeriesMeansTail.lean), [ArithmeticMeansBounds.lean](PowerLambert/ArithmeticMeansBounds.lean) |
| Positive lower word densities and disjunctivity | [Disjunctivity.lean](PowerLambert/Disjunctivity.lean) |
| Direct proof of nonnormality | [SeriesNonNormal.lean](PowerLambert/SeriesNonNormal.lean) |
| Explicit compact arithmetic model and measurable factor | [DynamicsModel.lean](PowerLambert/DynamicsModel.lean), [DynamicsFactor.lean](PowerLambert/DynamicsFactor.lean) |
| Weak convergence of the actual constant's orbit | [DynamicsWeak.lean](PowerLambert/DynamicsWeak.lean) |
| Atomlessness, full support and positive limiting frequencies | [DigitResults.lean](PowerLambert/DigitResults.lean) |
| Every finite partition has vanishing Shannon entropy rate | [EntropyZero.lean](PowerLambert/EntropyZero.lean), [EntropyResults.lean](PowerLambert/EntropyResults.lean) |
| Entropy definition and passage to measurable factors | [EntropyDefs.lean](PowerLambert/EntropyDefs.lean), [EntropyFactor.lean](PowerLambert/EntropyFactor.lean) |

Frequencies count all overlapping starting positions and converge along all prefix lengths. The empirical-measure sequence uses the first `N + 1` positions, so its denominator is always positive. This harmless reindexing is explicitly reconciled with the word-frequency definition.

Entropy uses PFR's ordinary Shannon entropy, the sum of `−p log p`. `ZeroMeasureEntropy` says that the normalized entropy of the joined iterates of **every** finite measurable partition tends to zero. The numeric `kolmogorovSinaiEntropy` takes the supremum of these asymptotic rates. The proof includes both this vanishing-rate statement and the equality of the numeric entropy to zero.

## Reuse and attribution

The Lean code is licensed under Apache 2.0. [PROVENANCE.md](PROVENANCE.md) records the mathematical sources and the vendored Shannon entropy library. Third-party copyright and author notices are retained. No author name is assigned to the accompanying result.
