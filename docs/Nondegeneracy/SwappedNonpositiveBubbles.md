# Nonpositive-height bubbles of the swapped route bases

Brundan–Ellis, arXiv:1701.04133v2, Definition 2.3, (2.16)–(2.18); route field
`NonpositiveBubbleField (swappedRouteBases sy)`.

## Closed forms (`SKM`, checked by CI)

For `h = hᵢ(μ) ≤ 0`, in `SwappedAssembly/SupportedRightBubbleCoefficients.lean`:

* `smul_bubRs_eq_cl_of_neg`: for `h < 0`, `c • bubRs(s) = cl(η·dots^(s-h-1) ++ ♦ε'·dots^(-h-1))`.
* `smul_bubRs_zero_of_eq_zero`: for `h = 0`, `c • bubRs(0) = 1`.
* `smul_bubRs_succ_of_eq_zero`: for `h = 0`, `c • bubRs(n+1) = -cl(η·dots^n ++ lcross ++ ε)`;
  here `ε'` is the leftward crossing followed by the undotted cap, and the sign is
  `-zsign(0) = -1`.
* `oddBubble_eq_smul_bubRs_of_nonpos`: for odd `i`, the odd bubble is `c • bubRs(1)`
  (at `h = 0` through `oddBubble_consistent`); hence `oddBubble_eq_cl_of_neg`,
  `oddBubble_eq_cl_of_eq_zero`.

## Action and assembly

* `VacuumEntry μ M hM a`: the `compDiag` entry of `cl M` at the vacuum sector of the tensor
  target family equals the coefficient action of `a` there.
* `closedAct_cl_eq_coefficient`: the closed-diagram-to-coefficient step of #1067.
* `VacuumRightEntries μ M N`: the six vacuum entries (even/odd colour, `h < 0` and `h = 0`, and
  the odd bubble), with coefficients the moments of `probeSeriesInv M`, their negatives at
  `h = 0`, and `±(-1)^(N_i+1) δ_i`.
* `vacuumRightBubbles_of_entries`: these entries give `VacuumRightBubblesNonpositiveHeight`
  for the supported action and the raw tensor coefficient action.
* `VacuumRouteSwappedNonpositiveBubbles.lean`: `SwappedRightEntriesField sy`,
  `nonpositiveBubbleField_of_entries`, and
  `nondegeneracy_of_swapped_positive_field_and_entries`.

## Remaining obligation

`SwappedRightEntriesField sy`: at each route index and colour with `h ≤ 0`, evaluate `compDiag`
of the cup–dots–♦cap diagram (and at `h = 0` the cup–dots–crossing–cap diagram) at the vacuum
sector, and identify it with the inverse-cap moments of `ELVTensorVacuumCapMoments`
(`tensorVacuumNegativeCap_odd_moments_*` and its even variants). The `h = 0`, `s = 0` entries
need no hypothesis (`coeff_zero_momentSeries`).
