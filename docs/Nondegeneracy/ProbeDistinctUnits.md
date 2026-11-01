# Direct distinct-colour probe units

`ProbeDistinctUnits.lean` constructs the actual source-corner sandwich through a target-corner inverse. Two dot slides and a unit leading term give both inverses of the following source-corner dot when the quadratic has a positive-dot remainder on each side. Separate left and right remainders are allowed; no commutation assumption between a remainder and the dot is required. The earlier single commuting remainder criterion remains available. No finite-dimensionality is used.

`ProbeMixedRelations.lean` defines the literal adjacent crossing between mixed word objects, derives its signed slides and quadratic identities, and supplies explicit right and left positive-dot remainder formulas before taking any quotient. The left remainder absorbs the supercommutation sign explicitly, so no extra Q coefficient support premise is introduced. The disconnected quadratic is the single unit constant.

The actual affine relations, target-dot signs and both leading-term units are now combined in ProbeAllUnits to prove units at every mixed-word position. The full stack and closed distinct-colour consumers passed full build, global axiom audit and non-vacuity checks before research integration in #807. This result does not identify a coefficient-specialized full action or its prescribed inverse matrices.
