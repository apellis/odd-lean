# Kernel matrices outside the target content

Current scope and verification are maintained in [STATUS](STATUS.md). Any original
topic-head pending checks below are historical; they do not override the consolidated
status or establish completion of the full conjecture.

DeformedMatrixComparison, section 4, requires one coefficient-presheaf matrix at a fixed target-content count before passing to arbitrary modules. This note records its zero-support branch.

For any moving colour (i), finite count (m), and old words (v,t) with different colour multisets, `ELVOffContentZero` makes both the ordinary Hom coefficient and the IndRes coefficient zero. The upper append-Hom coefficient also vanishes by multiset cancellation. Hence all Option-indexed source and target coefficient spaces of the prescribed finite matrices are subsingletons.

`actualPositiveKernelMap_bijective_of_content_ne` and `actualNegativeKernelMap_bijective_of_content_ne` prove bijectivity of the literal `actualPositiveKernelMap` and `actualNegativeKernelMap` components in this case. The result is generic in parity and finite count, including zero; it uses no height, chosen inverse, field, flatness or finite-colour hypothesis.

The producer and its paired consumer pass strict scoped checks. The consumer instantiates both moving parities, both matrix orientations, zero and nonzero counts, and distinct-content endpoints. Its audit covers all three owned declarations, including the private subsingleton-map lemma, with only the standard allowed axioms. Full repository CI remains the integration gate.

Matching-content coefficient bijectivity and its target-count assembly are separate obligations. This result does not assume them and does not assert arbitrary-module inversion.
