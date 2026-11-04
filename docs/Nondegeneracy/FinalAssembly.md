# Final assembly of the vacuum route

`OddMath/QuiverHecke/VacuumRouteNondegeneracy.lean` states the research-scope end
theorem as one conditional statement:

- `nondegeneracy_of_vacuum_route`: for a datum `D` with `sy : Symmetrizer D` and
  `H : VacuumRouteHypotheses D sy`, the Nondegeneracy Conjecture holds over every
  commutative ring with `2` invertible, for every homogeneous `Sc` and every
  `CScalars Sc`.

Proof chain (all checked): ground-ring descent
`SKM.nondegeneracyConjecture_of_charZeroField`; finite-colour reduction
`nondegeneracy_of_restrictColours_upward`; pairing-extension recovery
`PairingExtension.upwardCoefficientMap_injective_of_pairingExtension` at `(μ, 0)`;
bounded vacuum recovery `upwardCoefficientMap_injective_of_vacuum_evaluations` via
`VacuumRouteSector.toSwappedVacuumBlock` and
`SwappedVacuumBlock.toSwappedVacuumEvaluation`. The field form is
`nondegeneracy_of_vacuum_route_sectors`.

## Open route hypotheses

`VacuumRouteHypotheses` asks, over every characteristic-zero field, homogeneous `Sc`
and `cs`, for a `VacuumRouteSector` of the pairing extension of every finite-colour
restriction, at `(μ, 0)`, every equal-weight upward pair and every degree bound. Its
fields:

1. `VacuumBubblesPositiveHeight`: left-bubble series at colours with `hᵢ(μ) > 0`,
   even (`E_i(-z)/(1-z)^(M_i)`) and odd (`C_i(-z)/(1+z)^(M_i)`), and the odd bubble
   `(-1)^(N_i+1) δ_i`. The tensor-vacuum moments are checked
   (`InverseColumnOddSeries`, `InverseColumnEvenSeries`); the attachment to the
   cup/cap images of the constructed action remains.
2. `VacuumBubblesNonpositiveHeight`: the same at `hᵢ(μ) ≤ 0`.
3. `VacuumCoordinates`: the quotient ideal with weight bound
   `vacuumCutoff t d - 2·C(|t|, 2)` and the coordinate map on `V t'`.
4. `VacuumChartCoherence`: the literal evaluation law for every presented upward
   diagram (coefficient class at the identity, chart coherence in general).

`adjunctionBubbleSeries_of_heights` combines 1 and 2 into `AdjunctionBubbleSeries`,
whence (A16) by the infinite Grassmannian relations.

## Not yet done

The all-even specialization check against `SKM.EvenBridge.nondegeneracyConjecture_of_isEven`
is not part of this file; that theorem needs finitely many colours and
Khovanov–Lauda scalars, so the comparison of the completion criterion
(`FieldScopeBoundary.md`) is separate work.
