/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import LowerBoundCZ.AppendixE.Model
import LowerBoundCZ.AppendixE.Algebra
import LowerBoundCZ.AppendixE.Hierarchy
import LowerBoundCZ.AppendixE.Patching

/-!
# Appendix E — partial formalization (umbrella module)

Explicitly partial formalization of the SOS-hierarchy completeness argument
of Appendix E (`app:sos-convergence` in `main.tex`). See `AppendixE.md` for
the paper-to-theorem table and the full list of unformalized obligations.

* `AppendixE.Model` — measurable disk-control trajectories via an integral
  equation, physical vs. relaxed cost sets, `physicalInfimum`, and the
  conditional disk-equivalence / patching / zero-gap order lemmas.
* `AppendixE.Algebra` — augmentation matrix, Gram contraction to
  face-vanishing squares, scalar Schur step.
* `AppendixE.Hierarchy` — abstract value hierarchies and the
  common-certificate completeness theorem, instantiated at
  `physicalInfimum`.
* `AppendixE.Patching` — exact exponent arithmetic `b^{3/8}` error limit
  and the conditional `physicalInfimum ≤ T` conclusion.
-/
