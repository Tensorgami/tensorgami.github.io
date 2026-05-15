# Tensorgami

[![Verify Lean formalizations](https://github.com/Tensorgami/tensorgami.github.io/actions/workflows/verify-lean.yml/badge.svg)](https://github.com/Tensorgami/tensorgami.github.io/actions/workflows/verify-lean.yml)
[![Check site hygiene](https://github.com/Tensorgami/tensorgami.github.io/actions/workflows/check-links.yml/badge.svg)](https://github.com/Tensorgami/tensorgami.github.io/actions/workflows/check-links.yml)

Tensorgami is a public mathematical workbench for proof notes,
expository reconstructions, problem sets, and Lean-checked formalizations. Some
entries record new arguments, extraction formulas, or finite certificates;
others rebuild known results to make the mechanism explicit.

The archive emphasizes mechanism-level mathematics: explicit reductions,
normal forms, concrete decompositions, finite certificates, algorithmic
structure, and formal verification when it clarifies the argument.
Individual entries identify their contribution type so new constructions,
independent solutions, expository reconstructions, problem sets, and
Lean-checked formalizations are distinguished locally.

The site is published with GitHub Pages at:

```text
https://tensorgami.com
```

The repository is intentionally simple:

- `index.html`: homepage and archive
- `about.html`: about page, external links, and selected problem records
- `mechanisms.html`: mechanism map
- `verification.html`: verified artifacts, theorem names, and Lean checks
- `privacy.html`: analytics disclosure and browser opt-out
- `license.html`: reuse terms
- `notes/`: HTML landing pages for selected notes
- `styles.css`: global styling
- `pdfs/`: mathematical PDFs
- `tex/`: LaTeX sources for selected PDFs
- `formalizations/`: Lean sources
- `portfolio.json`, `llms.txt`: machine-readable summaries
- `scripts/check_internal_links.py`: internal link check for site pages
- `scripts/check_pdf_metadata.py`: metadata check for public PDFs
- `.github/workflows/`: Lean checks
- `LICENSE.md`: reuse terms

No build system is needed for the static site; GitHub Pages serves the files
directly, while GitHub Actions checks the Lean formalizations separately.

## Verify locally

Each Lean formalization is an independent Lake project. For example:

```bash
cd formalizations/pointwise-weighting
lake exe cache get
lake build
```

The same pattern applies in the other `formalizations/*` directories. The
formalization index gives the corresponding theorem names and build targets:

```text
formalizations/README.md
```

Internal site links can be checked with:

```bash
python3 scripts/check_internal_links.py
```

PDF metadata can be checked with:

```bash
python3 scripts/check_pdf_metadata.py
```

Contact: [hkshin@alumni.harvard.edu](mailto:hkshin@alumni.harvard.edu).

Selected problem records are listed on the
[About page](https://tensorgami.com/about.html), including the Bilkent
Mathematical Problem of the Month, November 2008, and IBM Ponder This records
from July and August 2010. Planned expositions or Lean formalizations are
identified as planned, not as existing verified artifacts.

Privacy and reuse terms are published at
[privacy.html](https://tensorgami.com/privacy.html),
[license.html](https://tensorgami.com/license.html), and
[LICENSE.md](LICENSE.md).
