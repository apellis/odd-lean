# The prescribed distinct mate under content comparison

Brundan–Ellis (1.12) must use the chosen positive crossing, unit and counit
after transport to fixed content. An arbitrary invertible map between the
two composites does not establish that assertion.

Fix lower content ν, two colours i,j, and an input module on content j+ν.
Use four append functors: j from ν to j+ν, i from ν to i+ν, i from j+ν
to i+j+ν, and j from i+ν to that same upper content. The last functor
`oldContentDistinctUpperAppend` retains literal append on words and arrows;
only the permutation certificate of the upper content changes.

`ELVInductionRectangularMate` defines the positive rectangular crossing
using the chosen induction-composition maps. Its mate uses the actual
upper j-adjunction unit and lower j-adjunction counit. On a complete
balanced tensor the output coefficient is

    crossing(j,i;s) ≫ twist_(p(i)p(j))(append_j(g)).

Neither g nor the input-module element is assumed homogeneous. This keeps
all exterior coefficient signs. The generic crossing and whole tensor formula and the prescribed-target
append producer pass strict scoped checks. The added generic mate-parity
lemma is being checked.

The selected source comparison is the chosen content i-induction
comparison followed by old i-induction of the chosen j-restriction
extension comparison. The selected target comparison is upper j-restriction
of the chosen i-induction comparison. On source tensors the former inserts
exactly the inclusion unit into the input coefficient. On target tensors
the latter inserts the same unit and keeps the entire crossing coefficient.
Consequently their square with the actual old distinct mate has the same
coefficient in the same order on every generator. The actual old mate
is inverted by `moduleMateIso`, so this square will attach its inverse
to the prescribed content operator without an extra invertibility input.

The content operator, chosen source/target chart isomorphisms and both
chart tensor formulas pass a strict producer check. The paired consumer
is proposed. The whole mate comparison and the consequent content
isomorphism remain to be checked. Canonical truncated-content and
original-weight transport are subsequent obligations.
