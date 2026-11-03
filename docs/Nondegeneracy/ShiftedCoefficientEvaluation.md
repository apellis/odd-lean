# Shifted reservoir component evaluation

`SwappedHomInversion.md` §3 (2)–(3) uses finite coefficient expansions at
each reservoir output block. A common nilpotence exponent on a whole
weight fibre is not needed.

`elvShiftedPostEndEvaluation` evaluates the total of a transformation on
`elvShiftedPostInduction`, then projects to the specified reservoir block.
The shift is the prescribed `homPiLeft` shift from
`ELVShiftedDenominatorUnits`. At shift zero the evaluation is the original
`elvPostEndEvaluation`. At shift one its component ring map uses the
product parity isomorphism and the parity twist; the shifted objects are
kept literally, without identifying them with the unshifted modules.

`elvShiftedPostEndEvaluation_dot_isNilpotent` transports the constructed
bound for the chosen reservoir postdot through that component ring map.
`elvShiftedPostEndEvaluation_probe_isUnit` sends the proved unit of an
explicit prewhiskered map `α` through postcomposition, the content shift
and evaluation. Neither result imposes finite support on the Hom object
or supplies an exponent independent of the input and output block.

`elvShiftedPostProbe_even_comm` derives commutation from the super
interchange law. `elvShiftedPostCoefficient_even_expansion` then gives the
finite negative geometric expansion of a coefficient `a`. This last
statement is an intermediate attachment: it exposes the single identity
`a * (Y - X) = 1`, to be supplied by the chosen crossing coefficient's
`CrossCoeff.IsInverse` proof. It does not yet identify `a` with the field
of a completed probe–reservoir package. The probe map `α` also remains
explicit until that package is instantiated.

The consumer uses the positive-level ELV action on its rank-zero
representable source, both content shifts, the identity preunit and the
constructed inverse of the shifted difference. Thus its coefficient
identity is proved by inverse cancellation. It also evaluates the chosen
odd reservoir postdot after both shifts for the connected asymmetric
two-odd datum. No odd coefficient expansion is claimed without a tested
odd preunit Hom object. All owned declarations are included in the axiom
allowlist audit.
