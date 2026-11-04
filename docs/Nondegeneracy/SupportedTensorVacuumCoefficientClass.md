# Raw coefficient classes on the tensor matrix vacuum

The target `tensorWordQuotientObservation_coefficient_vacuum` states that
the unchanged word-indexed canonical observation of
`tensorMatrixCoefficientAction a tensorMatrixVacuum` is precisely the
source quotient class of `sourceCoefficientHom a identity`. The source
ring is the full original `SYM D k`, including mixed parity. The
original cutoffs, literal power schedule and prescribed whole source and
target families remain unchanged. No nonzero or invertibility assumption
on the coefficient is imposed.

The argument first applies the actual full-matrix coefficient
observation square. Literal target labels are transported to the
specified source word through `tensorSourceLabels_colors`. A generic
chart-at-unit lemma then combines the actual vacuum source-chart unit
normalization with `PowerWordQuotientCoordinates.coefficient_unit_class`.
The coefficient-one case gives the canonical source identity class.

The concrete consumer uses two odd colours with a root-weight
collision. It proves that the class of `1 + delta` times the identity is
nonzero in the actual source quotient: the two coefficient/PBW basis
terms lie in a bounded window, their coefficient coordinate is nonzero,
and the existing half-turn window injection preserves it at cutoff 20
and the unchanged constant power schedule 20. The final observation
formula is applied to this same mixed coefficient and actual matrix
vacuum.

This is a raw coefficient observation statement. It does not identify
presentation bubbles, or their normalized substitution, with the
constructed coefficient action. That attachment remains a separate
input to the bounded-recovery square; no generator-detection or
nondegeneracy conclusion is asserted here.
