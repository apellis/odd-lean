# Raw mixed coefficient for arbitrary input functors

Current scope and verification are maintained in [STATUS](STATUS.md). Any original
topic-head pending checks below are historical; they do not override the consolidated
status or establish completion of the full conjecture.

The raw `(R,P)` coefficient ranges over an arbitrary functor `Z:B→Wx`.
The dotted-mate target-J construction only saw the special input `ΠH≫F`.
This topic retains the actual full-ELV weight-module categories and post-
induction, but removes that input restriction entirely.

For `E:A→B` with a homogeneous invertible probe dot `a`, use `E≫Z` as the
pre-induction functor and `a▷Z` as its unit endomorphism. The existing
arbitrary-functor post-induction denominator theorem gives the even linear
or odd square denominator unit after the prescribed Hom parity shift.
The coefficient is `(Y−X)⁻¹` at even colours and the numerator-first
`(X−Y)(X²−Y²)⁻¹` at odd colours. Dot-exchange anticommutation supplies both
odd identities; categorical inverse parity supplies colour homogeneity.

The module constructs one parity-indexed coefficient, both inverse
identities at either parity, and the parity statement for arbitrary Z. It
assumes no factorization through restriction and no full factor family.
Literal identification with `rpPreDot`/`rpPostDot` after the actual family
is instantiated remains an assembly step.

Concrete odd/even existing probe/full-ELV consumers pass strict checks. Their
probe degree matches highest parameter6 (odd multiplicity3, even6), and
the tested Hom shift is nontrivial. The source passes strict local checking
with warnings as errors. The consumer audits all 19 owned declarations,
including private/generated ones, against propext, Classical.choice, and
Quot.sound. Full CI is the integration gate.
