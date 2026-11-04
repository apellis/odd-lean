# Separated mixed bends in padded central charts

`Sigma/PaddedBendWindowEquations.lean` transports the separated equations
of `SwappedHomInversion` §3 (6) through the existing central source and
target corner charts. The output is the literal pair of equations used
by `CentralInverse/ResidualComparison`, with the specified
`centralPaddedProbeX`, `centralPaddedProbeY`, `centralPaddedCap` and
`centralPaddedUnit`.

`CentralPaddedDxSeparatedAt` is the equation for
`centralPaddedSigma ... true false`, with sign `-q^(r+1)`.
`CentralPaddedCxSeparatedAt` is the equation for
`centralPaddedSigma ... false true`, with sign `q^(r+2)`.
Both keep the exact integral exponent `-(r : ℤ)-1` and the same
normalized undotted probe cap or unit as the probe slide.

`centralPaddedDx_separated` transports any supplied raw Dx equation.
`centralPaddedCx_separated` transports the raw Cx equation when its
reservoir source and probe target are occupied. The two
`centralPaddedCx_separated_of_*_absent` declarations handle either
missing corner at every finite count by its proved zero-object
property. They impose no artificial support hypothesis on the padded
matrix.

The transport works for an arbitrary output functor into a preadditive
category and assumes the whole probe-dot isomorphisms. The series
producers use additive output evaluation. It constructs no coefficient inverse or
reservoir bound. The ELV specialization supplies those separately;
closed-error memberships and off-window contractions remain inputs
to the residual-comparison argument.

The producer and `scripts/NonVacuity/PaddedBendWindowEquations.lean`
pass strict scoped checks. The consumer derives the two raw bend
equations from the chosen ELV coefficient and its constructed inverse,
then transports them at both parity colours with a common count above
any requested height. Its occupied-corner validity conditions are proved
on the weighted-append fixture. Both absent-corner lemmas are applied at
the empty sector, and the fixture's probe append vector is proved
nonzero. The consumer audits all ten owned declarations against the
standard axiom allowlist.
