# Exact-content attachment of the chosen reservoir closures

[ELVReservoirClosures](../../OddMath/QuiverHecke/CyclotomicAction/ELVReservoirClosures.lean)
constructs the natural exact-content transformation needed in
[ReservoirClosureDegree](ReservoirClosureDegree.md), before its represented
integer degree is computed. Its `positive` and `negative` maps are literally

```text
unit₂ ; (dot₂^r ▷ F₂) ; chosenPrincipal ; (F₁ ◁ dot₁^s) ; counit₁.
```

Here `chosenPrincipal` is respectively `invPos.f'` or `invNeg.f'` of the
local record selected by `elvRouquierFamily.loc`. In particular, this file
does not replace that field by another matrix inverse or assume a
comparison with it. The unit, counit, and dots are the same chosen family
fields. There is no added sign or rescaling.

`positiveContent` and `negativeContent` are actual supernatural
endomorphisms of the identity on `ContentModules ... β.1`. Their total
components agree with the literal whole-weight closures at output block
`β` for **every** whole-weight family `M`, with input only `M β`.
The public comparisons are `positiveContent_total` and
`negativeContent_total`; equality is of whole module morphisms, hence
holds on every vector, without a faithfulness argument.

The block-dependence assertion is proved in
[ELVWeightCentreBlocks](../../OddMath/QuiverHecke/CyclotomicAction/ELVWeightCentreBlocks.lean).
Its `extension` places one exact-content module in block `β` and zero
modules in every other original-weight block. `restrict` applies a given
whole-weight identity transformation to this family and projects its output
back to `β`, with the canonical equality chart. Supernatural naturality
with the even inclusion `extension (M β) → M` proves `restrict_app`,
separately for both parity components. `restrict_total` then proves the
full comparison. This argument retains distinct content blocks with the
same original weight and requires no independent block-dependence premise.

`positiveCoefficient` and `negativeCoefficient` use the existing
`ModuleCentre.reconstruct`. Their realization acts as the chosen closure
on every input family, by `positiveCoefficient_total` and
`negativeCoefficient_total`. Thus the source-central reconstruction and
the final every-`M` equality in the closure target are now constructive.
No coefficient-degree hypothesis is used in this attachment.

The remaining degree input is the literal `positiveContent` or
`negativeContent` transformation evaluated on every representable and both
parities, of degree `2 * sy.d i * (r + s + 1)`. The criterion in
[ModuleCentreDegree](ModuleCentreDegree.md) then gives degree membership
of these recovered coefficients. Comparing the selected principal field
with the native represented inverse is still necessary for that degree
calculation. This file does not supply an integer grading on arbitrary
module morphisms or prove the positive-degree assertion itself.

The [paired consumer](../../scripts/NonVacuity/ELVReservoirClosures.lean)
uses actual rank-one odd data over the rationals, cyclotomic cutoff two,
coefficient cutoff three, highest weight two, middle weight zero, and
positive one-strand content. Both chosen principal inverse orientations
at height zero are tested for arbitrary `r,s`. The comparisons cover
every family `M`; the vector tests additionally use an actual representable
input with a surviving odd exterior class, proved nonzero after its
zero-extension chart. No nonzero output of a positive-degree closure is
asserted by this fixture.

Both producers and the paired consumer pass strict isolated checks. The
owned audits cover 24 declarations in `ELVWeightCentreBlocks` and 15 in
`ELVReservoirClosures`, using only the standard allowed axioms.
