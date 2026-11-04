# Finite bend windows at a fixed output content

The coefficient ideal in `ELVCategoryCoefficients` lives on the category
of all functors from a probe category into one exact reservoir-content
module category. A finite formula after selecting both an input module
and an output block does not by itself give a formula in that Hom
category: its truncation length must be independent of the input module.

The source bound in `ELVWeightDotBounds.elvWeightDotComponent_pow_zero`
has the required quantifier order. For each fixed output content `δ`,
there is a positive integer `n` such that the chosen dot's `n`th power
vanishes for every whole-weight input family. The exponent may vary
with `δ`; this does not assert a bound on a whole original-weight fibre.

`ELVOutputDotBounds` retains this same exponent under parity shift,
probe precomposition and reservoir restriction. Precomposition replaces
the input module by the image under the probe lowering functor.
Restriction reads the fixed successor content `blockSucc δ`, so its
source bound remains independent of the probe input. All these
transports are ring maps on endomorphisms and therefore preserve the
specified power-zero equation.

The `ELVOutputDotBounds` producer and paired consumer pass scoped checks
with Lean 4.34.1, warnings as errors and both repository compatibility
settings. All 10 owned declarations pass the standard axiom audit.
The consumer retains both moving parities, every content shift and
arbitrary input functors, alongside a detected nonzero probe vector.

The existing `RegularReservoir.evalHomFunctor` projects a reservoir
family to one content without evaluating the probe input. If the `n`th
power of an endomorphism vanishes at every input after that projection,
`supernatural_hom_ext_total` makes its whole projected `n`th power zero.
The total evaluation algebra homomorphism preserves powers and zero;
parity projections detect the original supernatural transformation.

`ELVProbeContentBends` applies these bounds to
the literal two mixed coefficient charts. Conjugation by their stated
isomorphisms preserves nilpotence. The generic separated-window
identities can then be evaluated with `evalHomFunctor` itself, rather
than its further evaluation at a probe module. Their terms and equality
therefore lie in exactly the Hom category of
`contentModuleCoefficientIdeal`, retaining every probe input module.
The two finite lengths can be increased to one common length above any
specified minimum, separately for each fixed output content.

The declarations `elvProbeDx_content_separated_windows` and
`elvProbeCx_content_separated_windows` supply the two literal equations.
`elvProbe_content_central_separated_windows_above` supplies them at one
common length above any chosen minimum. Its arguments contain an output
content but no input module. The named predicates
`ELVProbeDxContentSeparatedAt` and `ELVProbeCxContentSeparatedAt` reduce
to the exact `hDx` and `hCx` equations of `ResidualComparison`.

The producer and paired consumer pass scoped checks with Lean 4.34.1,
warnings as errors and both repository compatibility settings. The
consumer checks both moving parities at a specified nonempty central
sector, a common length at least seven, the source bound with its
uniform quantifier order, and a detected nonzero probe vector. All 50
owned declarations pass the standard axiom audit.

`ELVContentHomZero` supplies the zero object required by the padded
central charts in this exact category. It bundles the existing constant
zero-module functor and proves that its identity is the zero
supernatural transformation before any probe input is evaluated. The
resulting `contentHom_hasZeroObject` instance adds no hypothesis and
does not replace the coefficient category.

`ELVProbePaddedContentBends` transports the two equations into the
literal `centralPaddedSigma` entries used by the augmented central
matrix. Its source and target automorphisms are precisely the raw OLD
probe-dot units of `probeWindowX` and `probeWindowY`. Its undotted cap,
normalized unit and dotted reservoir windows are the padded factor
maps, with the signs `-q^(r+1)` for Dx and `q^(r+2)` for Cx retained.
`elvProbe_content_padded_central_separated_windows_above` gives one
common length above any minimum at every sector. If the reservoir
source or probe target is absent, the Cx equation holds in the padded
zero corner at every length, while Dx still supplies a sufficiently
long finite series.

Both additional producers and paired consumers pass the same scoped
strict checks. Their axiom audits cover all seven owned zero-object
declarations and all thirteen owned padded-bend declarations. The
padded consumer retains both moving parities, a nonempty occupied
central sector, both absent-corner branches, a common length at least
seven and a detected nonzero probe vector.

This supplies the category needed to use the chosen closure sandwich
lemmas and finite-sum closure of the first coefficient-ideal level.
It neither changes that ideal nor adds a global nilpotence hypothesis.
