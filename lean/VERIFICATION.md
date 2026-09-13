# Verification record

The complete formal statement is `PowerLambert.powerLambert_full_theorem`.

Both verification commands exited successfully with code 0. The clean build reported `Build completed successfully (3781 jobs)`; all guarded axiom checks passed.

- Lean: `4.34.0-rc2`, compiler commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- Mathlib: `de2ef68216c6074f338c8e61890ee0a379ddfb9b`.
- PFR Shannon entropy sources: `3d7898164ebff70a809dce618f9082a7b39e7850`.
- The project was rebuilt in a separate directory without copying any project build artifacts. Pinned dependency caches were reused.
- `lake build` and `lake env lean Audit.lean` are the reproduction commands, after fetching the Mathlib cache as described in the README.
- The final theorem's axiom dependencies are exactly `propext`, `Classical.choice` and `Quot.sound`. `Audit.lean` enforces this with checked expected output.
- No unfinished proofs, additional axioms or `native_decide` are used.

The verification covers every integer pair `b,r ≥ 2`, all finite words and all prefix lengths. It includes the actual Lambert-series definition, coefficient and carry identities, positive word frequencies, disjunctivity, irrationality, nonnormality, the explicit orbit limit, invariance, ergodicity, full support, atomlessness, and zero entropy for every finite measurable partition and in the numeric Kolmogorov–Sinai definition.
