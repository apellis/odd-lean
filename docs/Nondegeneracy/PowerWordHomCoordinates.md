# Whole Hom coordinates of the chosen E-word value

For SwappedVacuumCoordinates §§3–6, `homEquiv` is a linear equivalence
from whole maps out of the literal native E-word value to the cyclic
component of an explicit same-weight model word family. It wraps the
existing power-word Yoneda, cyclicity, and generator results through the
selected word chart. Unit evaluation is injective for arbitrary target
families; proved zero support includes all other product components.
Surjectivity for the model target uses the existing full old-arrow
generator and its constructed module map. The producer is
`OddMath/QuiverHecke/CyclotomicAction/ELVPowerWordHomCoordinates.lean`;
its only direct import is the established `ELVPowerWordCoefficients`.

The statements retain arbitrary finite colour sets, an additive weight
group, a commutative coefficient ring, the given datum and scalar family,
and arbitrary coefficient cutoffs and power schedules. Any requirements
of the datum and scalar structures are inherited unchanged. No
symmetrizer, homogeneous-parameter premise, field assumption, faithful
evaluation premise, or new action is supplied to construct these
coordinates. The target list may have different formal content at the
same weight: the proved zero-support statements still determine all
whole maps.

`homEquiv_from_old` gives the original full generator formula.
`homEquiv_coefficient`, `homEquiv_dot`, and `homEquiv_cross` give the
literal coordinates of the independently chosen A/T insertion, dot, and
both crossing colour cases. The native word-pair equality and recursive
chart join are proved by a generic categorical calculation before model
substitution. The actual target-path weight certificate and the required
equal-colour minus remain in the crossing formula.

The paired `scripts/NonVacuity/ELVPowerWordHomCoordinates.lean` consumer
constructs a nonzero whole native Hom from the
independently surviving exterior two-colour vector, verifies its evaluation,
and proves the actual selected cyclic unit is nonzero. It also tests a
different same-weight target word and the given coefficient, odd dot, and
equal/distinct crossing coordinate formulas. Strict source and consumer
checks passed; all forty-eight owned declarations use only the three
permitted standard axioms.

The construction introduces no action, quotient, or generic Yoneda theory.
It retains the finite-colour scope of the scheduled model. Equality on
the entire chosen upward presentation, attachment to the swapped Hom
corner, and the final observation kernel identification remain separate.
