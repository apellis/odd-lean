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
are retained. These two producers pass scoped strict checks, and their
first paired concrete consumer passes its scoped checks and 43-owned
axiom audit.

`ELVContentBlockRestrictionTensor` proves that the selected restriction
chart sends `[g ⊗ b]` to `[append(g) ⊗ b]`, with no homogeneity assumption.
This producer passes its scoped strict check.

The append extension tensor formula in `ELVContentBlockAppendTensor`
and its expanded paired consumer are proposed source. The remaining
append normalization is separated into flattening and insertion at
literal raw coend endpoints. These expanded sources still require their
strict checks. This note does not assert the canonical-content distinct
mate inverse or the original-weight factor action; those are the next
uses of these charts.
