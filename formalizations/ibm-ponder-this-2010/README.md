# IBM Ponder This July 2010

Lean formalization for `A Trace and Companion-Matrix Solution to the July 2010 IBM Ponder This Challenge`.

The main theorem is `IBMPonderThisFinal.ibm_ponder_this_main`, which verifies the divisibility statement

```lean
(1000000000 : ℤ) ∣ round (IBMPonderThisBridge.alpha ^ 21699999999)
```

where `alpha = 1 + 2 * Real.cos (Real.pi / 9)`.

The formalization checks the real/trigonometric rounding bridge, the companion-matrix congruence certificate, and the recurrence stitching lemma relating the two trace sequences.

It is checked with Lean 4.30.0-rc2 and mathlib v4.30.0-rc2.

```powershell
lake exe cache get IBMPonderThis.lean
lake build
```
