# Direct distinct-colour probe units

`ProbeDistinctUnits.lean` constructs the actual source-corner sandwich through a target-corner inverse. Two dot slides and a unit leading term give both inverses of the following source-corner dot when the quadratic has a positive-dot remainder on each side. Separate left and right remainders are allowed; no commutation assumption between a remainder and the dot is required. The earlier single commuting remainder criterion remains available. No finite-dimensionality is used.

`ProbeMixedRelations.lean` defines the literal adjacent crossing between mixed word objects, derives its signed slides and quadratic identities, and supplies explicit right and left positive-dot remainder formulas before taking any quotient. The left remainder absorbs the supercommutation sign explicitly, so no extra Q coefficient support premise is introduced. The disconnected quadratic is the single unit constant.

Remaining work: compare these actual affine relations with the rectangular corner criterion, normalize the target-dot sign, supply the leading-term units, and induct over all positions. No all-position mixed-word unit conclusion is claimed yet. Current consumers audit these modules; a closed actual distinct-colour unit consumer remains required. CI and integration reporting distinguish checked results from drafts.
