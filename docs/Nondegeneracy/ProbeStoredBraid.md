# Uncorrected braids on stored append cubes

Brundan–Ellis (1.9), outside the repeated-outer distinct-colour correction,
requires the three-crossing relation with arbitrary intermediate content
representatives.

`inductionCube_braid` is the generic twelve-edge balanced-induction
transport. It uses three lower append functors, two routes to each of
three pair vertices and three upper append functors. The six prescribed
`inductionTripleFlattening_prefix_rectangular` and
`inductionTripleFlattening_suffix_rectangular` squares compare the two
nested paths with the direct source paths. The generic lemma takes the
literal source equation as an explicit intermediate input.

`probeStoredBraid_source` supplies that input from the OLD quotient's
`tripleCross_braid`. The certificates at the eight content vertices are
arbitrary list permutations; their full OLD inclusions retain the same
coefficient arrows. `probeOldStoredBraid` then proves equality of the two
nested module paths with an independent factor `-1` at every equal-colour
pair and `1` at every distinct pair. The three scalars appear in reversed
order on the two sides and agree over the commutative base ring.

`probeStoredBraidLeft` and `probeStoredBraidRight` use the actual evaluated
`probeEvaluatedAppendTo` functors and `probeAppendToCrossComponent` maps.
The two `_native` lemmas retain their entire OLD module morphisms.
`probeStoredBraid` proves their equality under exactly
`¬ (i = l ∧ i ≠ j)`. There is no supplied braid, action, naturality or
flattening equation in either final concrete theorem. The acting scalar
family remains `parameterTwist D Sc`.

The consumer tests connected mixed even/odd data, two odd colours,
adjacent repeated colours and the all-equal case. Every chosen content is
append-indexed, with all twelve permutation certificates proved. A
nonzero admissible interior parameter is retained. One concrete test
evaluates the two three-crossing operators on every vector at every OLD
object; its regular probe input contains the explicit nonzero empty PBW
vector. Positive-level append witnesses are nonzero at both parities.
The audit covers all owned declarations in the generic, OLD and evaluated
modules.

The repeated-outer correction and the final whole-weight braid fields
are separate attachments.
