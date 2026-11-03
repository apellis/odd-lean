# Reversed reservoir word values on the original weight group

For a finite colour alphabet, `reservoirPath_value_heq` identifies the
literal reservoir induction word on its specified regular-power
empty-word family with `PowerWordEvaluation.value` at the reversed
colour list. This supplies the word-value comparison of
SwappedActionAssembly §6 and SwappedVacuumCoordinates §2. The source is
`CyclotomicAction/ELVReservoirWordValue.lean`.

An upward path from `(0,c)` to `(0,0)` has
`c = wordContent l`: each step removes precisely its head colour from
the reservoir content. Its original weight is therefore the
`blockWeight` of the reversed colour list. The proof retains the whole
weight group, including any common coroot kernel; it uses no injectivity
of the root map.

The induction starts with the explicitly given regular-power empty-word
family. For `l = a :: r`, the reservoir word applies the tail induction
and then the chosen induction of colour `a`. The comparison is
transported through that actual induction functor, and the existing
`value_append` gives the value at
`reverse(colours r) ++ [colour a] = reverse(colours l)`.
No initial-vacuum identification or factor-existence premise is assumed.

`pathValueAt` reindexes the same reservoir value along the proved
original-weight equality. `pathChart` then uses precisely the existing
`PowerWordEvaluation.chart`, with the equality transport prefixed.
`pathChart_hom_mem` proves its evenness on the whole weight product.

The producer and paired consumer pass strict scoped checks with the
pinned toolchain, warnings as errors and both compatibility settings.
The consumer uses the connected asymmetric two-odd-colour datum,
highest weight 20 and cutoff 20. It proves that an independent product of
two odd coefficients and the cyclic unit survive in the actual
reindexed reservoir path value. All 20 owned declarations, together with
all 105 declarations of the generic reservoir-word comparison, pass its
axiom audit. Full integration verification remains separate.

Attaching the eventual swapped tensor-vacuum Hom functor to this initial
family and identifying its literal layer action remain separate steps.
No swapped observation or nondegeneracy conclusion is claimed here.
See [ReservoirWordFunctor](ReservoirWordFunctor.md) for the checked
whole path-functor comparison.

