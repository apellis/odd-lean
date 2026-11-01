# Literal ordinary category and full scalar module descent

`ELVProbeOrdinaryCategory.lean` packages the existing `cycHom` quotients
as the Homs of `OrdinaryContentCategory D Sc a ν`, including the empty
content. This is an underlying additive linear category with precisely
those literal quotient Homs.

`probeOldOrdinaryFunctor D Sc m ν` is the actual full, additive linear
scalar specialization. Fullness uses the previously proved Hom
surjectivity. Its object lifting covers the entire target category.

For an actual scalar-evaluated old module,
`probeOrdinaryModuleFunctor D Sc m ν N hN` constructs the descended
ordinary module. Restriction along the full scalar functor is proved
exactly equal to `N.toFunctor`. The concrete input is provided by the
already checked actual probe coefficient-evaluation theorem.

Strict local producer and all closed consumers pass; all 92 owned
declarations pass the axiom audit. Consumers cover mixed content,
the literal elementary scalar -3, exact module restriction, and vacuum
fullness and object lifting. Full CI remains the integration gate.

No finite-colour hypothesis is required for this category/functor
packaging. The ordinary source super grading, the append commuting
square, and coend equivalence are separate successors. No ordinary
height-induction comparison or weighted coefficient evaluation is assumed.
