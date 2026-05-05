# Tensorgami

Tensorgami is a public mathematical workbench for original proof notes,
expository reconstructions, problem sets, and Lean-checked formalizations. Some
entries record new arguments, extraction formulas, or finite certificates;
others rebuild known results to make the mechanism explicit.

The archive emphasizes mechanism-level mathematics: explicit reductions,
normal forms, concrete decompositions, finite certificates, algorithmic
structure, and formal verification when it clarifies the argument.

The site is published with GitHub Pages at:

```text
https://tensorgami.com
```

The repository is intentionally simple:

- `index.html`: homepage and archive
- `about.html`: about page
- `mechanisms.html`: mechanism map
- `verification.html`: verified artifacts, theorem names, and Lean checks
- `notes/`: HTML landing pages for selected notes
- `styles.css`: global styling
- `pdfs/`: mathematical PDFs
- `formalizations/`: Lean sources
- `portfolio.json`, `llms.txt`: machine-readable summaries
- `.github/workflows/`: Lean checks

No build system is needed for the static site; GitHub Pages serves the files
directly, while GitHub Actions checks the Lean formalizations separately.

Contact: [hkshin@alumni.harvard.edu](mailto:hkshin@alumni.harvard.edu).
