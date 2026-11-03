# Principal inverse coordinates on supported content blocks

For the augmented matrices of Brundan–Ellis (1.13)–(1.14), the finite
forward fields determine the principal inverse. The local inverse record
need not be the one selected in the construction of the weighted matrix.

`contentSupportedLocalInverseFrom_principal` and
`contentSupportedLocalInverseTo_principal` identify the principal of every
record with the prescribed negative-crossing grid mate and every ordinary
unit/dot column or cap/dot row. The result is the principal of
`weightedContentLocalInverseFrom` or `weightedContentLocalInverseTo`,
conjugated by the specified `contentPrincipalTargetIso` and
`contentPrincipalSourceIso`. These charts are exactly the full-content
induction-square charts used by the forward comparison.

The proof uses the forward principal, unit-column and cap-row squares.
The finite forward columns jointly detect outgoing maps in the unit
orientation; the finite forward rows jointly detect incoming maps in the
cap orientation. After conjugation, the weighted principal has identity
product with the principal field and zero product with every auxiliary
field in its finite window. The corresponding local products force
equality. No comparison of inverse entries is assumed, and no choice is
unfolded.

`contentTargetsLocalInverseFrom_principal` and
`contentTargetsLocalInverseTo_principal` retain arbitrary stored contents
`β`, `γ`, `δ` and equalities `β + [i] = γ`, `γ + [i] = δ`.
This is the form needed by the supported weight-block induction functors.

The paired consumer tests both moving parities, positive and negative
content heights, and both orientations at height zero. A separate odd
rank-one singleton representable contains the nonzero exterior vector
detected by `truncatedSingle_delta_ne_zero`; both target principal
comparisons are instantiated on this occupied positive-content module.
The result is a principal-coordinate comparison, not an integer-degree
or coefficient-kernel theorem.
