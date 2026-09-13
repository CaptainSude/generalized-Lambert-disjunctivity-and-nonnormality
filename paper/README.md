# Read or rebuild the paper

[Read the six-page paper](power-lambert-digits.pdf), or edit [its LaTeX source](power-lambert-digits.tex). The bibliography is included in the same source file.

To rebuild the PDF, run these commands in this folder with TeX Live or MiKTeX:

```text
pdflatex -interaction=nonstopmode -halt-on-error power-lambert-digits.tex
pdflatex -interaction=nonstopmode -halt-on-error power-lambert-digits.tex
```

The [accompanying Lean package](../lean/README.md) proves all conclusions of the paper's main theorem. The paper uses the shorter entropy deduction of nonnormality; Lean also proves nonnormality directly from periodic approximation.

The paper has no author line and is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Citations credit the mathematical sources used.
