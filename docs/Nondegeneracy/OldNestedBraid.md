# The chosen crossing on nested old induction

Brundan–Ellis Definition 1.5 requires the braid for three separately
chosen induction functors. `ELVOldNestedBraid` compares them with direct
triple induction through the canonical `inductionComp` isomorphisms.
The same flattening identifies both independent double-crossing maps:
the prefix uses induction of the chosen first crossing, and the suffix
uses the chosen crossing at the already induced module.

The existing `inductionCompOfEq_assoc_hom` identifies the prefix-first
and suffix-first flattenings. The generic inner/outer transformation
comparisons in `ELVInductionGridDots` apply to the homogeneous crossing
as well as to a dot. Thus both chosen maps intertwine with the two direct
triple-induction maps whose braid is proved in `ELVOldInductionBraid`.
Transporting through the one common isomorphism proves the nested braid.
The three prescribed negative signs agree on the two sides, retaining
the literal `signedEqualInductionCross`.

The producer and concrete representable/shifted-module/nested-unit-tensor
consumer pass strict verification with warnings as errors and both
compatibility settings. The consumer audits all 20 owned declarations
against the standard axiom allowlist. Full integration remains pending.
The results concern
the untruncated old category; restriction to evaluated fixed contents and
weight products is a separate attachment, and no complete probe family
is asserted here.

The common flattening, intertwining and conjugation proof is now reused
from `ELVInductionGridBraid`. The old endofunctor statements and chosen
maps are unchanged. The refactored producer and its existing concrete
consumer pass fresh strict checks, auditing all sixteen remaining owned
declarations. This refactor awaits its own full integration gate.

The source head `2652d0a76a9ee31ee3c669eb1ad35736b837fee4` passed the
full build, global axiom audit and all concrete consumers in
[#1014](https://github.com/apellis/odd-lean/pull/1014)
([CI run](https://github.com/apellis/odd-lean/actions/runs/41691819623)),
merged at `2c1306c4`.
This verifies the original twenty-declaration source; the subsequent
shared-grid refactor has its separate strict paired check above.
