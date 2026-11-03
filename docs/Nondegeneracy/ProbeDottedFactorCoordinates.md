# Probe dotted factor coordinates

This supplies the probe cap rows and unit columns of the central
augmented matrix for the Brundan–Ellis inversion relation, in the
normalized precomposition convention of `SwappedHomInversion.md`, §2.

For every natural exponent n, every formal sector and every object Z of
the full Hom category, `epsEntry_probe_factor` identifies the literal
probe cap entry with `probeCapFactorIso.hom` followed by
`SKM.homReservoirCap`. Similarly, `etaEntry_probe_factor` identifies the
literal probe unit entry with `SKM.homReservoirCup` followed by
`probeCupFactorIso.inv`. The historical SKM names `homReservoirCap` and
`homReservoirCup` denote the normalized **precomposition** dotted
adjunction rows here. Their adjunction is the canonical inverse-defined
`T.leftAdjoints`, with inherited dot `T.dot` and no new gauge choice.

The proof starts with the existing diagonal-dot-power formulas for the
actual `epsEntry` and `etaEntry`. `capRow_dot_probe` and
`cupColumn_dot_probe` compute the selected probe dot layers in their
endpoint equality charts. The inner and return transports are then
composed into the prescribed probe factor charts. This includes n=0 and
requires no mixed-coefficient inverse, nilpotence or matrix-comparison
hypothesis. The probe cap has its always-present EF path; the probe unit
requires exactly the F-edge validity of its FE path.

`epsEntry_probe_coordinates` retains the sign
`koszulSign σ (1 + n * parity i)` when removing the source shift and the
inverse of `T.leftAdjScalar` at the source height on the raw left cap.
`etaEntry_probe_coordinates` retains the output-shift sign
`koszulSign σ (n * parity i)`, the left cup, associator and original dot
order. The signs and scalar remain explicit at height zero.

The paired consumer constructs both complete positive-level ELV factors
for the asymmetric two-odd datum. It instantiates both factor and literal
coordinate formulas at every exponent and both odd colours, on an
identity Hom containing an independently surviving product of the two
odd coefficients. It also instantiates all exponents on the canonical
mixed-content native probe height-zero sectors and checks their
nontrivial exponent-zero cap sign. All formal weight-product blocks are
retained.

These rows provide the probe window entries for the whole augmented
matrix comparison. They do not prove central invertibility or residual
coefficient-ideal closure, and use no nilpotence bound uniform over a
whole formal weight product.

The producer and paired consumer pass strict Lean 4.34.1 checks with
warnings as errors and both compatibility transparency settings false.
The consumer audits all 18 owned declarations against the standard
three-axiom allowlist.
