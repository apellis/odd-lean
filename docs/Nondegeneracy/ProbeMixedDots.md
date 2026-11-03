# Mixed probe and reservoir generator dots

SwappedActionAssembly F2–F3 requires the two prescribed dots on each
mixed `(R,P)` Hom object before constructing the coefficient in (A6).

`probeELVMixedBase` precomposes an input Hom object `Z` with the actual
`probeOldE` at the weight determined by the formal probe content `β`.
`probeELVMixedPreDot` is the original chosen `probeOldActionDot`, whiskered
by `Z`. Its parity is retained, and `probeELVMixedPreDot_isUnit` transports
the already proved whole probe-dot unit through this whiskering.

`probeELVMixedInnerDot` postinduces that map and applies the specified
`homPiLeft` content shift. `probeELVMixedOuterDot` is the chosen full-ELV
postdot under the identical shift. The two
`probeELVMixed_difference_isUnit` and
`probeELVMixed_square_difference_isUnit` theorems construct the even
`Y-X` and odd `X²-Y²` denominator units. Their inputs contain the actual
generators, a symmetrizer and homogeneous parameters. They do not assume
a denominator inverse, a nilpotence exponent or an action relation.
The construction uses the proved componentwise ELV bounds, without a
common exponent on a full weight fibre.

The source needs no completed multicolour package: its stated downstream
use is substitution into the literal fields of `elvProbeReservoir`.
There, the shift is `homContentShift D i β`.

The consumer fixes connected mixed even/odd and two-odd data, positive
probe and reservoir cutoffs and nonempty mixed formal probe content.
It checks the maps and both shifts for every ordinary input Hom object
`Z`, and separately retains nonzero original probe-append vectors at
both colours. It does not construct a nonzero coupled Hom object or a
vacuum observation; those are separate F5 obligations. All owned
declarations are included in the axiom allowlist audit.
