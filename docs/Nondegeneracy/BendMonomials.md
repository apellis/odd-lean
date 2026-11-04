# Mixed-bend monomials

The comparison required by `SwappedHomInversion.md` §3 (4)–(6) separates
an ordered inverse-probe/reservoir coefficient monomial into the existing
dotted cap and cup. `OddMath/SKM/RouquierHomBendMonomials.lean` treats the
literal shifted Hom functors and their prescribed adjunctions.

For the probe-to-reservoir bend, the insertion is the dotted reservoir
cup at the probe cap's source, followed by the image of the negative
probe cap. Supernaturality of the reservoir cup moves the cap to the
left. Their parities are `r p` and `(r+1) p`; their product is zero in
`ZMod 2`. Thus this separation contributes no sign.

For the reservoir-to-probe bend, move the inverse probe power across the
undotted reservoir counit, which is even. The naturality of the probe
unit then separates the dotted reservoir cap from the negative probe
cup. This separation also contributes no sign. The additional `q`
in the final PR monomial comes from the coefficient's mixed-interchange
chart, and the bend itself retains its prescribed minus sign.

`homPreDotAut` packages the raw probe dot and its whiskered inverse as
an automorphism. `homPreNegativeCap_aut` and `homPreNegativeCup_aut`
identify the existing windows with the literal exponent `-(r : ℤ)-1`
used in `CentralInverse/ResidualComparison.lean`. These identities hold
on arbitrary Hom objects. The consumer specializes them to the complete
scalar probe and truncated ELV reservoir at both parities, with probe
dot invertibility proved from the construction.

The raw monomial identities do not themselves supply the four mixed
coefficient-chart dot comparisons or a finite reservoir bound. Those
comparisons connect them to `Sigma/FiniteBendEvaluation.lean`; the
componentwise bounds belong to `ELVProbeFiniteBends.lean`.
