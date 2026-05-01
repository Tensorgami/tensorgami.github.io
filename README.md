# Tensorgami

Tensorgami is a public archive for mathematical writing: expositions,
problem sets, proof notes, and Lean-checked formalizations.

Proof-focused entries often pair the PDF exposition with Lean source files
and automated CI checks, so readers can inspect both the argument and the
formal verification when it is available.

The site is published with GitHub Pages at:

```text
https://tensorgami.github.io
```

The repository is intentionally simple. The homepage is built from
`index.html` and `styles.css`; papers live under `pdfs/`, and Lean projects
live under `formalizations/`.

No build system is needed for the static site; GitHub Pages serves the files
directly, while GitHub Actions checks the Lean formalizations separately.
