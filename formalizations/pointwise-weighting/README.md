# A Weighting Argument for Pointwise Convergence to Convergence in Measure

Lean formalization accompanying the Tensorgami note `A Weighting Argument for
Pointwise Convergence to Convergence in Measure`.

The verified file is `PointwiseWeighting/Basic.lean`.  It currently contains:

- a finite-measure Egorov wrapper for uniform convergence away from a small exceptional set;
- a countable Egorov cover and boundedness stratification;
- the conull-uniformization theorem by a strictly positive measurable weight;
- the dominated-convergence weighting proof on sigma-finite measure spaces;
- the real-line specialization for Lebesgue measure.

The Lean formalization verifies the main conull-uniformization conclusion and
its convergence-in-measure consequence.  The PDF also presents an Egorov
double-series construction as an exposition of the same weighting mechanism.
