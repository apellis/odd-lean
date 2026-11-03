# Deferred whole content mate conversion

The checked tensor comparison is in `ContentAppendMate.md`. The whole
module conversion here is proposed only and is not imported into the
checked library.

`ELVContentMateSquare.lean` proposes the equality

`orderedGridMateComponent ≫ chosen following-E/F chart = chosen preceding-E/F chart ≫ restricted matrixMateComponent`.

The source is the preceding induction/restriction composite at content
`i :: ν`; the target is the following restriction/induction composite at
that content. All categories are untruncated old content categories.
The proposed proof uses raw coend factories, a generic restriction-total
bridge, an intermediate restricted-mate tensor identity and induced-source
extensionality. The final joins elaborate, but kernel normalization of
the native module records still exceeds the default deterministic limit.
The paired consumer is proposed and has not checked against this producer.
No theorem from this module is claimed.

`ELVContentEFParity.lean` proposes evenness of the selected E/F charts.
The one-letter extension and restriction-extension arguments reduce to
checked even induction-composition and adjunction components. Conversion
of the selected append-restriction composition still reaches the default
recursion limit, so the module remains unchecked and unexported.

The direct matrix route does not require either deferred conversion.
The selected E/F and fully faithful value isomorphisms give genuine
underlying linear equivalences. Together with the checked prescribed
mate tensor identity and dotted cup/cap identities, they can establish
bijections of the given grid matrix components. The prescribed matrices
are already even, so component inverse construction and cancellation
recover even inverse maps and input naturality without assuming chart
evenness.

The coordinatewise family helper previously present in this proposal is
now checked with its concrete consumer; its argument is recorded in
`FiniteSupermoduleFamilies.md`. It does not establish the chosen content
matrix inverses. Both matrix signs, zero-count cases, contents without a
predecessor, permutation reindexing and passage to the coefficient-truncated
weight action remain separate obligations.
