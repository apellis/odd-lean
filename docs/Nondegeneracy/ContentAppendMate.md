# The prescribed content mate and the old first matrix entry

DeformedMatrixComparison (2), (4) uses the ordered ordinary-adjunction
cup-crossing-cap operator as the first entry of both matrices. Fix a word
ν, colour i and content γ=i::ν. Let J append i from ν to γ and K append i
from γ to i::γ. These are the selected old-content append functors.

`oldContentEqualCross` is the literal old last equal crossing restricted
to J⋙K. Its supernaturality has degree p_i². The given
`orderedGridMateLinear` composes the actual upper unit, minus the crossing
conjugated by the selected induction flattenings, and induction of the
actual lower counit. Its tensor formula is

```
[g ⊗ b] ↦ [-(cross_s ≫ twist_(p_i²)(K.map g)) ⊗ b].
```

No compatibility equation or invertibility hypothesis is supplied to this
operator. Its definition retains the prescribed crossing and extra minus.

For a module N at γ, use the previously selected preceding E/F chart A_N
and following F/E chart B_N. The checked source formula is

```
A_N([g ⊗ b]) = [g ⊗ unit_inclusion(b)].
```

The following chart is restriction of the selected append comparison,
including its fully faithful inclusion unit. The public theorem
`oldContentAppendRestrictionLinear_mate_tensor` identifies

```
B_N(m_content([g ⊗ b])) = m_old(A_N([g ⊗ b])).
```

Here m_old is exactly `matrixMateComponent`, the literal first entry used
by the old finite unit and cap matrices. The identity p_i²=p_i identifies
its prescribed parity. Both sides have the same crossed coefficient and
the same actual inclusion-unit vector. In particular neither coefficient
arrows nor module vectors are required to be homogeneous, and no column
or row is rescaled.

The concrete consumer uses mixed representables, both moving parities,
the original append dot and identity-plus-dot coefficients, and arbitrary
module vectors. Pure contents of lengths one, two and three at cutoff four
exercise the corresponding heights 2, 0 and −2, with the height equalities
proved in the consumer.

The formal public comparison is on every balanced generator. The whole
operator and finite matrix natural-isomorphism attachment, including
parity/product coordinates and dotted unit/cap entries, remain subsequent
steps. This intermediate statement uses a preceding block through
γ=i::ν. The absent-predecessor case still needs its zero preceding
composite before an all-content matrix theorem is asserted.
