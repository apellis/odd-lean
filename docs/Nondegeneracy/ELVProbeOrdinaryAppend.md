# The actual scalar specialization append square

`ELVProbeOrdinaryAppend.lean` constructs right append on the literal
ordinary `cycHom` quotient content category. It is additive and linear.

`probeOldOrdinaryFunctor_append D Sc m ν i` proves the exact equality

`oldContentAppend ⋙ Q_upper = Q_lower ⋙ probeOrdinaryAppend`.

Every map is the existing canonical old append or the literal ordinary
quotient right context. The equality uses the previously proved actual
scalar right-context formula, not an assumed natural comparison.

Strict local producer and all closed consumers pass; all 16 owned
declarations pass the axiom audit. Consumers check mixed content,
the actual right-appended word, and both odd and even append from the
vacuum. Full CI remains the integration gate.

This provides the concrete square for the generic induction-composition
comparison. The ordinary source super grading and final comparison with
existing height induction remain separate. No weighted coefficient
truncation is specialized.
