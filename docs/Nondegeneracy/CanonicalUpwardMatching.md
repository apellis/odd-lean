# Canonical PBW words as actual matching choices

`OddMath/SKM/CanonicalUpwardMatching.lean` supplies the matching-family input
for the PBW comparison with BE2 §8. Its skeleton is

```lean
(canWord n w).reverse.map (fun p => TMove.mv (Move.cross p))
```

The reversal is essential: `QuiverHecke.cw` reads the Coxeter word bottom first
in reverse list order. `crossing_pairing` proves that the bottom position `j`
is paired with top position `wordProd n σ j`, even when colours repeat.

The reducedness proof uses no independence assumption. Every valid positional
word is an actual matching, and its endpoint state is computed directly.
For a reduced Coxeter word, choose the existing strictly reduced realization
of its pairing. Positive strict realizations contain only crossings, so extract
a positional word from that realization. Its endpoint permutation agrees with
the initial word product. Minimal Coxeter length therefore bounds its number
of crossings below. The matching crossing-count bound in the opposite direction
forces the initial word to be weakly reduced. Crossing-only syntax has no
critical points, hence it is strictly reduced.

`members` consists of the canonical words with the prescribed actual boundary.
`members_unique` recovers the permutation from the pairing. `members_complete`
extracts the permutation of any strict positive representative and replaces its
word by the canonical Coxeter word. `choice` packages these facts with existing
bounded strand points and serializers into a genuine `MatchingBasisChoice`.

For the literal lists used by the quiver-Hecke basis, the exported interface is:

- `choiceList t t' h`, where `h : t.length = t'.length`;
- `choiceList_word t t' h R`, the canonical permutation of a member;
- `choiceList_word_spec`, equality of the actual member word with the reversed
  canonical crossing list.

Any preferred serializer, including the bottom-sorted PBW serializer, can now
be chosen using the checked matching-choice transition. This module does not
prove faithfulness of the upward SKM representation or bubble separation.

The module passes a targeted warnings-as-errors build. Its concrete consumer
uses three equal colours and a non-involutive three-cycle, so the endpoint test
detects reversal errors that colour labels alone would miss. It also verifies
that the literal-list canonical family is nonempty. Printed axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.
