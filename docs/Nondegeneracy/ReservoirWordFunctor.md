# The reservoir induction word of a vacuum path

SwappedActionAssembly §6 and SwappedVacuumCoordinates §2 identify the
surviving upward path with the reservoir induction word. The source is
`SwappedAssembly/ReservoirWordFunctor.lean`.

`ReservoirWord.word` constructs this word using only `RouquierData` and
the reservoir highest weight. For a path between `(0,c)` and `(0,d)`, it
is a one-morphism from weight `-Λ + α(d)` to weight `-Λ + α(c)`. The empty
word is the identity; the head induction follows the tail induction, as
recorded by `word_nil` and `word_cons`. Thus the labelled word is read in
reverse order when compared with an append-defined native E-word value.

For an already supplied `ProbeReservoir P`,
`P.reservoirWordFunctorIso` identifies the entire path functor with
postcomposition by this word. The comparison uses the actual
postcomposition associators and unitors. Probe content remains zero at
every step, so every content-parity shift is zero.
`reservoirWordFunctorIso_hom_mem` proves that the comparison is even,
retaining odd generators without an additional transport sign.

The producer passes a strict scoped check. Its paired consumer tests the
P-free induction-word construction on noncommuting superfunctors: swap
two superspaces, and duplicate the first superspace. The canonical path
with colours `[false,true]` reads swap before duplicate. On scalar
components `(2,3)` it retains the nonzero scalar 3; the opposite order
gives scalar 2. The consumer passes strict checks and audits all 105
owned declarations.

These bare generator data are not claimed to be a full action. A second
consumer section supplies two constructed full-ELV factors with cutoff
four and the exact highest-weight pairing. It applies the whole-functor
comparison to a two-colour path and its evenness to the identity Hom
input. Both the producer and this complete paired consumer pass strict
scoped checks, including all 105 owned-declaration axiom checks. The
identical factors are a concrete test of this comparison, not a claim of
a separating model. Full integration verification remains separate.

The specialization to the selected full-ELV regular-power word value
remains open. It must retain the reverse
word and the existing chosen chart, without assuming the desired vacuum
comparison. No swapped observation or nondegeneracy conclusion is claimed.

The source head `2652d0a76a9ee31ee3c669eb1ad35736b837fee4` passed the
full build, global axiom audit and all concrete consumers in
[#1014](https://github.com/apellis/odd-lean/pull/1014)
([CI run](https://github.com/apellis/odd-lean/actions/runs/41691819623)),
merged at `2c1306c4`.
