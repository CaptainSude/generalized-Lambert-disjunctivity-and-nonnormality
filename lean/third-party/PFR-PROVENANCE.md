# PFR Shannon entropy dependency

The 27 Lean files in `PFR/` are the transitive PFR import closure of
`PFR.ForMathlib.Entropy.Basic`, copied from the Polynomial Freiman–Ruzsa
formalization project at commit `3d7898164ebff70a809dce618f9082a7b39e7850`.
They retain their original namespaces and are licensed under Apache 2.0;
see `PFR-LICENSE` in this directory.

They are compiled against this project's pinned mathlib commit
`de2ef68216c6074f338c8e61890ee0a379ddfb9b` using Lean 4.34.0-rc2.
This dependency supplies the ordinary finite Shannon entropy, data-processing,
and entropy subadditivity results. The dynamical block-entropy arguments are
in `PowerLambert/Entropy*.lean`.

Source: https://github.com/teorth/pfr
