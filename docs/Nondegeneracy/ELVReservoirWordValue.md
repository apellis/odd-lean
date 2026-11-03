# Reversed reservoir word values on the original weight group

The next attachment for SwappedActionAssembly §6 and
SwappedVacuumCoordinates §2 compares the literal reservoir induction word
with `PowerWordEvaluation.value` at the reversed colour list. The source
preparation is `CyclotomicAction/ELVReservoirWordValue.lean`.

Its private helpers passed a strict scoped check before adding the
unverified chosen-value draft below. An upward path from
`(0,c)` to `(0,0)` has `c = wordContent l`: each step removes precisely its
head colour from the reservoir content. Consequently its original weight
is the `blockWeight` of the reversed colour list. This equality retains
the whole weight group, including any common coroot kernel; no
injectivity of the root map is used. The actual chosen `elvE` objects
also transport across equal source and target weights and heterogeneous
equalities of their input modules.

The remaining proposed induction starts at the explicitly given
regular-power empty-word family, not an arbitrary initial Hom functor
equipped with a vacuum-identification premise. For `l = a :: r`, the
native reservoir word first applies the tail word and then the chosen
induction of colour `a`. Apply the inductive comparison through that
actual induction functor. The existing `value_append` then identifies the
result with the value at `reverse(colours r) ++ [colour a]`, which is
`reverse(colours l)`. The proved original-weight equality supplies the
endpoint reindexing. Composing with `PowerWordEvaluation.chart` must use
that same selected chart and its proved evenness.

The source now contains this induction as the unverified
`reservoirPath_value_heq` draft. Its paired consumer draft applies the
selected-value identification at highest weight 20 and cutoff 20. Its chosen
target retains a nonzero two-odd-colour coefficient and a nonzero cyclic
unit under the prescribed chart. The draft `pathChart` uses precisely
the existing chosen chart after the proved weight reindexing; its
evenness is also supplied. The consumer pulls that nonzero unit back to
the actual reindexed native path value. Complete producer and consumer checks
remain unfinished; the consumer's claims above describe its intended
checks, not verified results.
The checked helpers do not identify a swapped layer action, construct a
factor pair or supply an observation. The separate generic path-functor
comparison and its exact consumer boundary are recorded in
[ReservoirWordFunctor](ReservoirWordFunctor.md).
