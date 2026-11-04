# Mixed denominators on the OLD-probe and ELV-reservoir pair

SwappedActionAssembly F2–F3 and (A6) require the mixed crossing entry on the
specified factor pair. `elvProbe_rpObj`, `elvProbe_rpPreDot`, and
`elvProbe_rpPostDot` identify its literal RP carrier and chosen dots with the
shifted ELV induction, inner probe dot, and outer reservoir dot. These are
identities of the chosen operators, including the prescribed shift.

`elvProbeCrossDenominatorUnits` constructs both denominator units on that pair:
the even difference and odd difference of squares. It uses the whole OLD-probe
dot unit and the existing reservoir bounds at individual content components.
No uniform nilpotence exponent over a weight fibre is assumed.

`elvProbeCrossCoeff` is the crossing coefficient selected from these denominator
units. `elvProbeCrossCoeff_isInverse` proves its even inverse and odd
square-denominator identities. `elvProbeCrossCoeff_isSupernatural` derives its
prescribed parity and naturality from those identities and the constructed
denominator units; it adds no nilpotence hypothesis. The component evaluation
map and its inner-unit/outer-nilpotence theorems retain the literal RP carrier.

The paired consumer uses a two-colour mixed-parity datum and an asymmetric
all-odd datum, applies both denominator and coefficient identities, checks
supernaturality of the constructed coefficients and supplies nonzero vacuum
vectors for the acting twisted probe parameters. Every owned declaration is
audited against the repository axiom allowlist.

The finite coefficient expansions are developed separately in
[ELVProbeCoefficientExpansion](ELVProbeCoefficientExpansion.md), using this
constructed coefficient and its proved inverse identity.

These statements construct the mixed crossing coefficients. Finite bends and
the complete swapped action remain separate assembly obligations.

The producer and paired consumer pass scoped checks with the pinned toolchain, warnings as errors and both compatibility settings. The consumer audits all 38 owned declarations against the repository axiom allowlist. Both mixed-parity and connected two-odd factor pairs instantiate the constructed units, inverse identities and supernaturality theorem.
