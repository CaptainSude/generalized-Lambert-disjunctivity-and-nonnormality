# Sources and dependencies

The formalization uses Lean `v4.34.0-rc2` and Mathlib commit `de2ef68216c6074f338c8e61890ee0a379ddfb9b`, with the transitive dependency revisions recorded in `lake-manifest.json`.

The `PFR/` directory contains the 27-module dependency closure of `PFR.ForMathlib.Entropy.Basic`, copied from the [Polynomial Freiman–Ruzsa formalization](https://github.com/teorth/pfr/tree/3d7898164ebff70a809dce618f9082a7b39e7850), commit `3d7898164ebff70a809dce618f9082a7b39e7850`. These sources provide Shannon entropy, conditional entropy and their inequalities. Their original author notices are retained; the license is reproduced in `third-party/PFR-LICENSE`. They are compiled against this package's pinned Mathlib version.

The arithmetic argument in the accompanying mathematical work develops methods from:

- D. Duverney, *Arithmetical functions and irrationality of Lambert series*, AIP Conference Proceedings 1385 (2011), 5–16. [Author manuscript](https://danielduverney.fr/documents/theorie-des-nombres/TokyoNT.pdf).
- D. Duverney and Y. Tachiya, *Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*, Forum Mathematicum 31 (2019), 1557–1566. [Author manuscript](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf).
- J. Vandehey, *On an incomplete argument of Erdős on the irrationality of Lambert series*, Integers 13 (2013), A58. [arXiv:1206.0340](https://arxiv.org/abs/1206.0340).

Background for the arithmetic compact-group viewpoint:

- F. Cellarosi and Ya. G. Sinai, *Ergodic properties of square-free numbers*, Journal of the European Mathematical Society 15 (2013), 1343–1374. [Journal article](https://ems.press/journals/jems/articles/11437).
- F. Cellarosi and I. Vinogradov, *Ergodic properties of k-free integers in number fields*, Journal of Modern Dynamics 7 (2013), 461–488. [arXiv:1304.0214](https://arxiv.org/abs/1304.0214).

Circle representatives and empirical word-frequency transfer follow the constructions in our earlier verified XiNormality/Cylinder and XiNormality/Weyl work; the necessary arguments are included here. This package has no dependency on those earlier projects.

The formal proof establishes its own entropy argument: periodic measurable sets generate the arithmetic model's Borel sigma algebra; finite labels admit periodic approximations; a rare-error encoding bounds finite Shannon block entropy; entropy passes through the actual measurable factor. It does not assume a general entropy theorem absent from Mathlib.
