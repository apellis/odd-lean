# Two-letter coend square comparison

This implements the generic flattening calculation for chosen crossing
transport in [DeformedActionAssembly](DeformedActionAssembly.md), sections
5–6. It retains the literal ordinary-right coefficient order before
specializing the two-letter comparison to weighted modules.

Two squares `J ⋙ Q = Q ⋙ T` and `K ⋙ Q = Q ⋙ S` give
`coendSquare_comp_eq`. The inverse object map for the composite is `S`
applied to the first inverse object map, followed by the second inverse
object map (`coendSquare_comp_endpoint`). Naturality of the second square
gives `coendSquare_comp_coefficient`: the product of the two quotient
coefficients is the quotient coefficient of `K.map a ≫ g`, in that order.

`coendSquareMap_comp_tensor` compares the canonical raw map for this
composite square with both induction-composition flattenings. Applied to
`[g ⊗ [a ⊗ b]]` and then flattened, the composite raw map is exactly the
flattening of `[coefficient_K(g) ⊗ [coefficient_J(a) ⊗ b]]`.
No comparison map is supplied as an extra premise. Neither coefficient
arrow nor the module vector must be homogeneous. No flatness or scalar
specialization is assumed.

The producer and paired consumer pass strict scoped checks. The consumer
uses the actual old-to-weighted quotient on a mixed induced representable,
all moving-colour pairs, arbitrary output arrows and vectors, two specified
odd dot coefficients, and vacuum with literal unit input. All 11 owned
declarations pass the axiom allowlist audit. Full CI is a separate gate.

The concrete selected double-append comparison must still be identified
with the canonical raw map by its literal generator formula. Injectivity
of the target canonical flattening then gives its nested tensor formula.
The chosen crossing application and content/weight transport remain
separate obligations; this calculation alone does not supply a factor action.
