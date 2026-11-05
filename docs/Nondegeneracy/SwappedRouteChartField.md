# Chart coherence of the swapped route bases

Scope: `FieldScopeBoundary.md`; Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §8. Continues `SwappedVacuumCoordinates.md` §§2–7.

## Statement

For a symmetrizer `sy` of `D`, the route field `ChartField` of `VacuumRouteFields`
holds for the swapped route bases:

* `swappedCoordinateField sy : CoordinateField (swappedRouteBases sy)`;
* `swappedChartField sy : ChartField (swappedRouteBases sy) (swappedCoordinateField sy)`

(`OddMath/QuiverHecke/VacuumRouteSwappedCharts.lean`).

## Argument

1. *Layer observations.* On the canonical quotient observation of the tensor matrix
   module, the literal dot, equal-colour crossing and distinct-colour crossing layers of
   the full chosen action multiply the observed class on the right by the original
   affine generator in the contexts read off the layer
   (`tensorMatrixQuotientObservation_dot`, `_sameCross`, `_cross`). Each is the
   composite of the literal layer entry, the equality-transport form of the layer cell,
   the global/local chart identification, and the contextual class square.
2. *Corner evaluation.* At a target word `t` the evaluation is the observation along the
   all-reservoir vacuum path when the formal content of `t` equals that of the source
   word, and zero otherwise. Generating layers permute colours, so they preserve content;
   on the remaining words both sides of the square vanish because the transformed ideal
   is closed under right composition. The vacuum value is the coefficient observation of
   the vacuum (`tensorCornerEvaluation`).
3. *Transport.* The evaluation is built at `probeHW - reservoirHW` and transported to
   the sector weight `(μ, 0)` along `weight_difference`; its ideal is unchanged.
4. *Vacuum window.* The ideal is the transformed ideal of `e_j ^ c` with
   `c = vacuumCutoff t d`. Each `e_j` has coefficient weight at least one, so each power
   has weight at least `vacuumCutoff t d`, and `transformedIdeal_le_vacuumWindow` places
   the ideal in `ExtendedAtLeast (vacuumCutoff t d - 2·C(|t|,2))`.

`VacuumCornerEvaluation.chartCoherence` then gives `VacuumChartCoherence` at every
route index. No hypothesis beyond the route index is used.

## Remaining route fields

`PositiveBubbleField` and `NonpositiveBubbleField` for the same bases are not addressed
here.
`nondegeneracy_of_swapped_bubble_fields sy hp hn` assembles the conjecture from these two
fields for `swappedRouteBases sy`, using `swappedCoordinateField sy` and
`swappedChartField sy` for the other two.
