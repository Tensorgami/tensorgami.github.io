# Tensorgami Lean formalizations

These are Lean/mathlib formalizations accompanying selected Tensorgami notes.
Each folder is an independent Lake project pinned to its own Lean toolchain and
`lake-manifest.json`.

## Verified artifacts

| Note | Lean theorem | Subject | Mechanism | Project |
| --- | --- | --- | --- | --- |
| Divisibility of Separated Polynomials | `SeparatedPolynomialDifferences.sep_dvd_iff_exists_common_outer` | algebra | normal forms, descent | `separated-polynomial-differences` |
| A Galois-Theoretic and Frobenius-Descent Viewpoint on a Polynomial Composition Law | `SeparatedComposition.separated_composition_criterion_iff` | algebra | generic fibers, Frobenius descent | `galois-frobenius-composition-law` |
| Extracting the First Prime Greater than m | `ExtractingFirstPrime.extractedPrime_is_smallest_prime_gt` | number theory | gcd filtering, finite certificate | `extracting-first-prime` |
| A Note on Disjoint Decompositions of [0,1) into Closed Sets | `no_pairwiseDisjoint_closed_iUnion_eq_Ico` | analysis/topology | compactification, Baire category | `disjoint-decomposition` |

## Build

From any individual project directory:

```sh
lake exe cache get
lake build
```

The repository also runs the same checks through GitHub Actions:

```text
.github/workflows/verify-lean.yml
```
