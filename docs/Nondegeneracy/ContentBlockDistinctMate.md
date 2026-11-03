# Distinct mates on canonical truncated content modules

Brundan–Ellis (1.12), DeformedActionAssembly §4: the prescribed positive
rectangular cup-crossing-cap is invertible on the actual multiset-indexed
`ContentModules` of `TruncatedCategory`. For arbitrary `β`, its input
content is `β + [j]` and output content is `β + [i]`. Its sole additional
hypothesis is `i ≠ j`. No flatness, finite-colour, or auxiliary
invertibility assumption is imposed.

`ELVFullInductionSquareSource` fixes the chosen full induction square,
its even input-module isomorphism, ordinary restriction coordinates,
and output-object transport while the categories remain abstract.
`ELVFullContentMateSquare.fullContentMate_square` identifies the whole
rectangular and ambient mixed mate maps. Its intermediate hypotheses
are coefficient compatibility for the four commuting inclusion squares
and the chosen restriction chart's unit formula. Ordinary coend balance
retains the entire right action and every coefficient parity.

`ELVContentBlockDistinctMate` supplies the literal positive crossing,
its supernaturality, the even chosen restriction-extension chart, and
the selected source tensor formula. Concrete statements use the generic
chart maps directly, retaining the inclusion object transports.

`ELVContentBlockDistinctInverse.contentBlockDistinctMateLinear_square`
discharges both intermediate chart conditions for the canonical content
inclusions. The whole coefficient is the positive crossing followed by
the twist of the entire appended arrow, of degree `parity i * parity j`.
`contentBlockDistinctMateLinear_bijective` transfers the proved global
truncated PBW inverse through the chosen source and target charts.
`contentBlockDistinctMate_isIso` and
`contentBlockDistinctMateFunctor_isIso` assert invertibility of the
specified module map and its whole input-natural family. The two
`Inverse_mem` declarations retain the crossing degree for the selected
generic homogeneous inverses. No concrete source-map wrapper changes
the selected forward operator.

All four producers and their paired concrete consumer pass scoped strict
checks. The consumer covers both mixed orders, distinct odd colours,
parity-shifted representables at the input content, whole isomorphism
roundtrips, odd input-map naturality, an exterior coefficient together
with its identity sum, and empty lower content at zero cutoff. All 161
owned declarations pass the axiom allowlist audit. Integration CI
remains pending.

This is the canonical truncated-content rectangular mate inverse.
Original-weight assembly, including absent-predecessor components and
identification with the selected weight crossing, remains next. This
result alone does not assert the complete categorical factor action.
