# The chosen central augmented inverse on supported inputs

`Sigma/PaddedResidualInversion` now proves
`SupportedSectors.centralFactorMatrix_content_isIso` and
`centralAugmentedMatrix_isIso` for the intended ELV probe/reservoir pair
and its constructed mixed coefficient. The producer and concrete
nonzero two-odd collision-block consumer pass strict checks; all nine
owned declarations pass the standard axiom audit. Full integration is
separate from this scoped evidence.

These results implement SwappedActionAssembly §6 and SwappedHomInversion
§§3–6 at every supported input. They require the standing cutoff/weight
matches, a positive integral symmetrizer and homogeneous parameters.
No inverse, bend expansion, coefficient-ideal membership or nilpotence
premise remains. Both height-zero orientations are included.

The input belongs to the exact-content supported full subcategory.
This does not assert `P.CentralInvertible` on every object of the larger
ambient `P.H t`. Root-weight collisions can leave other contents occupied
at a formally absent corner. The checked support arguments supply the
native zeros used for padding.

## The literal matrices

Fix colour i, sector t, a supported object Z, and ν=P.wt t. Let H=D.h i ν.
At a fixed output content δ, evaluation retains the entire input
superfunctor. The prescribed source and target charts identify the
actual matrices with

    M+ : XR ⊕ XP → YR ⊕ YP ⊕ O^H,
          XR ↦ [sR, Cx, vR(a)],
          XP ↦ [Dx, sP, rowP(a)],

    M- : XR ⊕ XP ⊕ O^(-H) → YR ⊕ YP,
          XR ↦ [-sR, -Cx],
          XP ↦ [-Dx, -sP],
          Oa ↦ [uR(a), colP(a)].

`AugmentedSectorEntries` and `AugmentedFactorMatrix` retain every
principal, mixed and finite-window entry in these squares. The negative
matrix has all four principal entries negated and unchanged unit
columns. `pureSourceSign` in `SeparatedClosures` is the prescribed source
diagonal (-1,-1,1); its checked square is identity. This transfers
invertibility after the normalized probe slide is used with its original
sign. No sign is reassigned to the factor adjunction or dot.

## The inverse inputs are constructed

`SupportedFactorWindowInverse` and `ReservoirWindowInverseData` supply
the four factor windows and their named principal/finite-slot entries,
including absent corners. `SupportedProbeSlideWindow` supplies the
actual probe dot automorphisms, signed slide and every cap/unit power.

The chosen reservoir principal closures have reconstructed source degree
2*d_i*(r+s+1). The finite-slot boundary coefficient has degree
2*d_i*(r-j), positive for r>j. `ELVReservoirClosureIdeal` and
`ELVReservoirBoundaryIdeal` place the literal native actions in level one
of the content coefficient ideal, with arbitrary surrounding maps.
`ReservoirWindowCoefficientIdeal` attaches these to the named padded
inverse entries. Its consumer retains a nonzero absent unit window;
that branch is not replaced by zero. Finite-window contractions are the
Kronecker equations of the specified inverse.

`ELVProbeContentBends` and `ELVProbePaddedContentBends` give the exact
signed separated sums for Cx and Dx. A common finite length is chosen
uniformly over input modules at each fixed output content. It need only
exceed the reservoir window length. Principal closure membership holds
for every dotted index, so fused rows outside the series range remain
covered. `SeparatedClosures` derives the three mixed closed-error
memberships by finite sums without grading arbitrary module Homs.

`SignedResidualWindows` covers all six combinations of fused, reservoir
and probe height signs. In particular `ResidualComparisonNegative`
attaches the negative probe-height subcases (b), (c). The reference
inverse entries lie in level zero because the concrete content ideal
contains every morphism there. Its joint nilpotence follows from the
bounded source coefficient grading.

## Product assembly and remaining use

`centralFactorMatrix_content_isIso` applies the signed residual theorem
in the category of whole functors into the fixed-content module category.
`centralAugmentedMatrix_isIso` then uses the literal augmented chart
squares and `RegularReservoir.isIso_of_eval` to assemble over every output
content. Each content may have its own series length and ideal bound.
No uniform bound over an original-weight fibre, regular-input
replacement or independence of roots is used.

Next extract the leftward entries and presentation relations on supported
inputs and their supported path values. `LeftwardData` stores objectwise
generator images: an inverse-or-zero construction can define those
images on the ambient category while proving the inverse identities
only where supported invertibility is established. Offcentral sectors,
whiskered relations and the final vacuum/bubble observations remain
separate attachments. The central inverse alone is not the full swapped
action or nondegeneracy theorem.
