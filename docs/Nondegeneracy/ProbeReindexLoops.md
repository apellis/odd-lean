# The local loops under content reindexing

The local inverse relations in Brundan–Ellis (1.13)–(1.14) compare the two
loops at the intermediate content. Let `h₁ : (i :: ν).Perm ν₁` and
`h₂ : (i :: ν₁).Perm ν₂`. Reindexing the standard intermediate category
`i :: ν` to `ν₁` sends the standard lower and upper loops to endofunctors
canonically isomorphic to the loops for the actual stored-target append
functors.

`probeReindexLowerLoopIso` is the lower append comparison precomposed with
the chosen lower restriction. `probeReindexUpperLoopIso` is the upper
append comparison precomposed with inverse intermediate reindexing and
postcomposed with the chosen upper restriction. Their endpoints agree by
the strict restriction squares: reindexing changes only permutation
certificates. Both isomorphisms have even components by the checked
evenness of the append comparison and parity preservation by restriction.
There is no independent choice of a comparison on either loop.

The consumer applies both comparisons and their inverse identities to the
two-colour rational fixture with a mixed source list, reordering each new
letter to the end, and checks evenness for both parity choices. These
comparisons identify the local loop objects; a local inverse record for
the selected stored-target generators additionally requires their mate
and dotted unit/counit compatibility squares.
