# Reservoir closures in the source coefficient image

For BE (1.13)–(1.14), closure dependency G8, the degree calculation concerns
coefficients of the literal closures selected by `elvRouquierFamily`.
[ELVReservoirClosureDegree](../../OddMath/QuiverHecke/CyclotomicAction/ELVReservoirClosureDegree.lean)
contains the coordinate and degree statements below.
The source category has an integer grading; arbitrary morphisms between
ungraded reservoir modules do not need one.

Fix a datum `D`, homogeneous scalars `Sc`, a symmetrizer `sy`, a cutoff
matching the highest-weight pairing, adjacent steps `x₀+αᵢ=x₁` and
`x₁+αᵢ=x₂`, and an arbitrary output block `γ` at `x₁`. For dot powers
`r,s : ℕ`, put `d = 2 * sy.d i * (r+s+1)`. The declarations

- `ReservoirClosures.positiveCoefficient_mem_degree`, for `0 ≤ D.h i x₁`;
- `ReservoirClosures.negativeCoefficient_mem_degree`, for `D.h i x₁ ≤ 0`,

place the chosen closure's reconstructed coefficient in
`contentCoefficientDegree D Sc cutoff N γ.1 sy hc d`. These statements
cover every output block, including blocks with no lower predecessor.
They add no inverse-comparison, module-grading or represented-action
hypothesis.

The existing `positiveCoefficient_total` and `negativeCoefficient_total`
equations in
[ELVReservoirClosures](../../OddMath/QuiverHecke/CyclotomicAction/ELVReservoirClosures.lean)
identify the realization of each named coefficient with the corresponding
whole-weight closure on every input family:

```text
(contentRealize c).total (M γ) = t_rs.total M γ.
```

Thus the named coefficient itself supplies the witness combining prescribed
degree and action on every input. The symmetrizer positivity `sy.pos i`
and `r+s+1 > 0` make its degree strictly positive. This is the attachment
needed by the source coefficient ideal; it does not assert a grading of
all module endomorphisms or the final nondegeneracy theorem.

## Supported output blocks

If `γ = blockSucc D Λ i h₁ β`, the proof follows the prescribed finite
forward matrices and their selected inverses.

1. `positive_content_coordinates` and `negative_content_coordinates`
   identify the literal chosen unit, principal inverse and cap with their
   exact-content fields, using the existing forward-coordinate squares.
2. `contentTargetsUnitClosure_coordinates` and
   `contentTargetsCapClosure_coordinates` transport those fields through
   the stored-successor charts. `positive_weighted_coordinates` and
   `negative_weighted_coordinates` retain the selected weighted local
   inverse records. The content crossing height is the negative of the
   categorical weight height, so the two orientations are exchanged.
3. `weightedContentUnitClosureValue_evaluate` and
   `weightedContentCapClosureValue_evaluate`, in
   [WeightedContentKernelClosureCoordinates](WeightedContentKernelClosureCoordinates.md),
   identify the closure action with its raw OLD kernel coefficient on
   every vector of the induced truncated module.
4. `positiveRepresentedValue_degree` and
   `negativeRepresentedValue_degree` use the shared represented-coefficient
   degree equations. These apply `ELVKernelClosureDegree` and preservation
   of degree by the quotient at each literal word, then transport the
   typed coefficient to arbitrary stored content.

`positive_represented_coordinates` and
`negative_represented_coordinates` combine these comparisons on every
whole-weight input family. Extending an arbitrary exact-content module
into that family then gives `positiveContent_represented_coordinates`
and `negativeContent_represented_coordinates`. These are equations of
the total action on every module vector, without a separate parity or
integer-grading premise on that module.

## Outputs without lower predecessors

[ReservoirAbsentClosure](ReservoirAbsentClosure.md) proves that the chosen
whole-weight closure vanishes whenever

```text
¬ ∃ β, blockSucc D Λ i h₁ β = γ.
```

The lower induction component is zero, hence the final counit component
is zero, independently of the principal inverse and dot powers.
`positiveContent_total_absent` and `negativeContent_total_absent`
transport this vanishing to every exact-content module. Zero belongs to
the required source degree. This argument retains formal content; it
uses no injectivity of the map from content to weights.

## Reconstruction

[ModuleCentreTotalDegree](ModuleCentreTotalDegree.md) proves
`ModuleCentre.reconstruct_mem_degree_of_total_evaluation`: the total
action on the identity of each representable determines the source
integer degree of the reconstructed coefficient. Each source parity
component is recovered by the corresponding parity projection, which
preserves the independent source integer grading. Applying the supported
or absent calculation above at every representable identity proves both
all-output coefficient degree statements.

The paired consumer applies both coefficient statements at an occupied
odd one-strand quotient, both moving parities in a connected asymmetric
datum, strictly signed heights and absent-predecessor vacuum outputs.
The odd identity and exterior vector are independently detected as
nonzero. It audits every declaration owned by the producer against the
standard axiom allowlist. Full package CI remains the integration gate.
