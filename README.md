# Tensorgami

Tensorgami is a public mathematical workbench for expositions, proof notes,
problem sets, and Lean-checked formalizations. The archive emphasizes
mechanism-level mathematics: explicit reductions, normal forms, concrete
decompositions, finite certificates, algorithmic structure, and formal
verification when it clarifies the argument.

The site is published with GitHub Pages at:

```text
https://tensorgami.com
```

The repository is intentionally simple:

- `index.html`: homepage and archive
- `about.html`: about page
- `mechanisms.html`: mechanism map
- `styles.css`: global styling
- `pdfs/`: mathematical PDFs
- `formalizations/`: Lean sources
- `.github/workflows/`: Lean checks

No build system is needed for the static site; GitHub Pages serves the files
directly, while GitHub Actions checks the Lean formalizations separately.

Contact: [hkshin@alumni.harvard.edu](mailto:hkshin@alumni.harvard.edu).
