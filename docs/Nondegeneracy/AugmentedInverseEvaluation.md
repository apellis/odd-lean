# Evaluation of augmented inverse matrices

Brundan–Ellis (1.13)–(1.14) supplies finite homogeneous row and column
inverse matrices. Whole supernatural inverse records must retain those
five identities when evaluated on a module.

`superfunctorTotalEvaluation N` is the additive, linear superfunctor
which evaluates a whole supernatural transformation at its total component
on `N`. It preserves composition and identity. For a homogeneous map of
parity `p`, that total is its `p` component.

`SuperSumInvTo.at J N` and `SuperSumInvFrom.at J N` evaluate the given
whole inverse record. Their forward principal map is literally
`f.app p N`; their forward dotted entries are `(g m).total N`. The inverse
principal and dotted entries are `J.f'.total N` and `(J.g' m).total N`.
The four `_at_f'` and `_at_g'` lemmas retain these entries by reflexivity,
for every natural index, including indices outside the finite window.
Both constructions preserve the common parity profile, the total identity,
the principal identity and all three orthogonality identities. They apply
to arbitrary source and target supercategories and to height zero.

The consumer evaluates a constructed three-slot odd inverse at the
nonzero rational unit super vector space. It checks all five matrix
identities in both orientations, proves the evaluated principal inverse
and both dotted inverse entries nonzero, and tests the empty window and
out-of-window retention. The owned-declaration audit uses the standard
axiom allowlist.
