# The append adjunction at arbitrary OLD content representatives

Brundan–Ellis (1.12)–(1.14) require the given append adjunction at canonical
multiset representatives, while the stored-content inverse constructions
use cons lists. `ELVProbeReindexInduction` supplies their adjunction comparison
without an inverse or compatibility premise.

For permutations h:ν→μ and h':ν'→μ' and actual append certificates
i::ν→ν', i::μ→μ', the OLD functor square is literal: appending and then
reindexing equals reindexing and then appending. The module reindexing
functors are strict inverse equivalences. Their adjunction unit and counit
are identities.

`oldAppendReindexIso` compares induction-then-reindexing with
reindexing-then-induction. It is the canonical `leftAdjointUniq` comparison
of the two composite adjunctions with their identical right adjoint.
Both directions are even. `oldAppendReindexIso_unit` and
`oldAppendReindexIso_counit` retain the actual composite units and counits;
there is no freely chosen gauge.

`probeAppendReindexIso` restricts this same comparison to the full evaluated
probe categories. Both endpoints already preserve the prescribed coefficient
evaluation by append and reindexing closure. Its forward and inverse retain
the literal OLD maps, including naturality on odd input maps.

The paired consumer uses connected even/odd data, actual regular probe
modules, a nontrivial change of the base list and a canonical upper list.
It checks both evenness directions, both inverse identities, the unit/counit
squares and odd-input naturality. The producer and paired consumer pass
strict scoped checks with warnings as errors and both compatibility
settings, including the axiom audit of all 45 owned declarations. Full
integration verification remains separate. Transport of the chosen dots and crossings,
and the resulting local and distinct inverse records, remain separate.
