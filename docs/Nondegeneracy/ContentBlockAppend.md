# Full-content charts after coefficient truncation

The canonical `ContentModules` in Brundan–Ellis (1.12) are modules on the
multiset-content full subcategories of `TruncatedCategory`. They differ
from the untruncated list-indexed `OldContentModules`.

`ELVContentBlockExtension` supplies the literal content inclusion, its
chosen fully faithful unit, extension supported at the prescribed
multiset, and the actual even inclusion counit isomorphism on supported
modules. Truncated quotient arrows vanish between unequal contents.
`ELVContentBlockAppend` gives the chosen append extension comparison by
induction composition and the literal append/inclusion square. The
restriction extension comparison uses this square, the inclusion unit,
and the supported inclusion counit. Arbitrary common target contents
are retained. `ELVFullInductionSquare` evaluates the exact selected induction
composition comparison followed by the chosen full-inclusion unit while
all four functors are abstract. `ELVContentBlockAppendTensor` specializes
that raw map to the canonical truncated content category.
`contentAppendToRestrictionLinear_eq_selected` identifies it literally
with the previously chosen content chart.
`contentAppendToRestrictionLinear_tensor` sends `[g ⊗ b]` to
`[g ⊗ unit(b)]`. `ELVContentBlockRestrictionTensor` sends the restriction
chart tensor `[g ⊗ b]` to `[append(g) ⊗ b]`. Both formulas retain entire
quotient arrows with no homogeneity assumption.

All five producers and their paired concrete consumer pass scoped strict
checks. The consumer uses actual parity-shifted truncated modules,
both moving parities, exact multiset contents, whole selected chart
roundtrips, both tensor formulas, literal selectedness, and the zero
cutoff and empty content. All 77 declarations owned by the producers
pass the axiom allowlist audit. Integration CI remains pending.

The canonical-content distinct mate inverse and the original-weight
factor action are the next uses of these charts.
