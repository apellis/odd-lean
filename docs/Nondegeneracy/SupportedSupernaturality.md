# Supernaturality and interchange on retained Hom inputs

The inverse-entry step in `SwappedActionAssembly.md` §3 and (A7)
requires naturality on the inputs used by the representation. Let
`Sₜ` be the full subcategory of retained inputs in the raw Hom category,
with inclusion `Jₜ`. Every summand path preserves these objects.

The positive augmented matrix, restricted along `Jₜ`, has entry
parity depending only on its target index: the principal parity is
`pᵢ²`, and the dotted cap row has parity `n pᵢ`. The five local inverse
identities at every object of `Sₜ` give both matrix inverse equations
there. `MatrixInverse.isSupernatural_of_inverse_target` then proves
that the selected inverse entries are homogeneous and natural on
`Sₜ`. The negative matrix uses the analogous source-dependent parity
and `isSupernatural_of_inverse_source`. These are the two inputs to
`Supernatural/RestrictedLeftward.lean`.

This argument applies to the conditional raw leftward data because
at each retained input its augmented matrix is proved invertible.
The zero choice at other raw inputs plays no role. A full subcategory
retains all arrows between its objects, so both even and odd input
morphisms are covered. At height zero the positive matrix supplies
the principal inverse; the diamond windows are empty.

`SupportedInterchange.lean` restricts the existing interchange
calculation to a path-closed input property. Its exchange lemma uses
naturality only at the two intermediate retained objects. The native
path-closure theorem supplies those objects from a retained rightmost
input. Thus generator supernaturality on the retained full
subcategories suffices for the original layer representation's
interchange law.

The concrete `SupportedSupernaturality` attachment uses the chosen
ELV coefficient and `pointwiseLeftwardData`. The unequal-colour
`SigmaPermutation` input is kept explicit at this intermediate step;
its discharge belongs to the separate mixed-crossing construction.
The attachment does not assert generator naturality or augmented
invertibility on all raw Hom objects.

The generic `RestrictedLeftward` producer and its concrete consumer pass
strict scoped checks. All seven owned declarations pass the standard
axiom audit. The consumer uses the chosen ELV coefficient on a proved
nonzero supported odd path, with heights `2` and `-2`, checks the inverse
entries' homogeneous parts, and applies both naturality orientations to
a proved nonzero odd parity-shift isomorphism of supported inputs.

The generic `SupportedInterchange` producer and its consumer also pass
strict scoped checks, auditing all four owned declarations. That
consumer restricts the chosen upward generators to the retained full
subcategories and applies interchange to a constructed retained family
whose selected one-odd sector is proved nonzero. Its path-closure and
generator-naturality premises are supplied by the construction.

The concrete `SupportedSupernaturality` producer and the direct
applications in `RestrictedLeftward` also pass strict scoped checks,
auditing all 28 owned declarations against the standard axiom allowlist.
The consumer applies the chosen equal-colour crossing at arbitrary
outer sectors and applies its chosen cup and cap naturality directly
to the nonzero odd input isomorphism. No local inverse or raw-global
naturality hypothesis is supplied. The concrete interchange theorem
retains exactly its stated unequal-colour permutation input.
