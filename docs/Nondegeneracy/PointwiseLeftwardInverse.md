# Pointwise leftward inverse entries

Brundan–Ellis Definition 1.5 (1.13)–(1.14) defines the equal-colour
leftward crossing and diamond cups/caps as entries of the augmented
inverse. The raw `ProbeReservoir.LeftwardData` has objectwise generator
entries. It carries no naturality or inversion field.

`leftwardOfPointwiseAugmentedInverse` follows that structure directly.
At each raw input it chooses the family inverse of the corresponding
`augPosMat` or `augNegMat` if that particular matrix is invertible, and
uses zero otherwise. All three families are zero off the matched
rightmost weight. The positive crossing entry is minus the inverse's
principal entry; the negative crossing entry has no extra minus.
Cup and cap entries beyond the finite window are zero.

`PosInverseAt` and `NegInverseAt` state the five matrix identities at
one specified input. The two corresponding
`leftwardOfPointwiseAugmentedInverse_*InverseAt` theorems derive them
from a local matrix `IsIso`, the weight match, and the appropriate
height sign. No inverse at every raw Hom object is a hypothesis.

`LeftwardData.IsInverseAt` states the ten equal-colour inversion
relations at a fixed input, before whiskering. Its conversion theorem
uses the five positive or negative identities at that same input for
all colours and leftmost sectors. At height zero the negative
relations follow from the positive inverse, as in the existing
global inverse-entry argument.

The module constructs raw data without asserting raw-global
`AugmentedInvertible`, `LeftwardData.IsInverse`, or naturality.
Supported inputs supply local invertibility separately. Restriction
to supported source objects and their path images is the setting for
the subsequent uniqueness, parity and whiskering arguments.

`SupportedPointwiseLeftwardInverse.lean` specializes this choice to
`elvProbeCrossCoeff` as `SupportedSectors.pointwiseLeftwardData`.
Its two central inverse theorems apply to every supported Hom input.
They discharge the local matrix isomorphism with
`centralAugmentedMatrix_isIso`; only the appropriate height sign
remains. This specialization gives the five central equations and the
off-weight normalization, rather than a raw-global inversion claim.

Both producers and `scripts/NonVacuity/PointwiseLeftwardInverse.lean`
pass strict scoped checks. The consumer constructs a nonzero supported
one-odd reservoir path using the half-turn coefficient coordinates.
Its two colours have heights `2` and `-2`, so both finite windows are
nonempty. The selected data satisfy all five identities in each sign,
and their cup and cap families are each proved not identically zero.
The consumer also checks the off-weight normalization and derives all
ten local unwhiskered presentation identities at every outer sector of
this nonzero supported input, using `SupportedAugmentedInverse`.
It audits all 42 declarations owned by `PointwiseLeftwardInverse` and
all 14 owned by each of `SupportedPointwiseLeftwardInverse` and
`SupportedAugmentedInverse` against the standard axiom allowlist.
