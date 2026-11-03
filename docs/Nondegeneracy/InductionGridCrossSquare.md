# Square-zero double induction crossing

For Brundan–Ellis (1.7), `gridDoubleCrossComponent_square` transports the
literal square-zero source crossing through the chosen induction
composition isomorphism. `inductionModuleCross_square` gives the equation
for the specified negative crossing as a two-morphism on the entire input
module category. `inductionModuleCross_total` retains the exact chosen
module crossing under evaluation.

The producer and concrete old-content consumer pass strict scoped checks.
All three declarations use only the standard three Lean axioms. The
consumer supplies the literal old affine quotient square-zero relation
and the full-coefficient old representable, for both moving parities.
No local inverse or complete action family is assumed.
