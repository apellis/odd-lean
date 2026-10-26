# Content-shifted Hom sectors and the remaining coordinate comparison

## Scope

The modules `RouquierHomContent`, `RouquierMateProjection`, `RouquierMateSlide`,
`RouquierMateSeries` and `RouquierMateCoordinates` separate the algebraic
projection calculation from its categorical realization. They do not close
A2. In particular, a proof of the named predicate
`SuperRouquierLoc.MateProjectionFormula` for arbitrary supplied coordinates
is not a construction of those coordinates in a reservoir–probe action.

## Finite content and original weights

Retain finite contents `β₊, β₋ : I →₀ ℕ` together with

```
-μ₊ = λT + Σ_i β₊(i) α_i,     μ₋ = λW + Σ_i β₋(i) α_i.
```

The Hom sector is `Hom(T(-μ₊), W(μ₋))`, at original weight `μ₋ - μ₊`.
The content parity is `P(β) = Σ_i β(i) p(i)`. The chosen asymmetric convention
shifts postcomposition by `E_i` by `p(i) P(β₊)`, while precomposition by `E_i`
is unshifted. Adding reservoir colour `j` changes the postcomposition shift
by `p(i)p(j)`; this is `homContentShift_add_single`. Finite content is not
silently identified with its image in the weight lattice.

The implemented postcomposition right adjoint has Π on its input side. Its
adjunction follows by composing the factor right adjunction with the
self-adjunction of Π. This is a genuine adjunction on the full Hom category,
including odd morphisms. `RouquierHomContentCoherence` moves Π to the output
side through the even β comparison, preserving homogeneous supernaturality.
The resulting `homContentPostOutAdjunction` uses the same output-shift
convention for both adjoints. The comparison is not an unsigned identification:
Π self-interchange is negative, and the integral parity-envelope fixture
proves that it differs from the identity.

Raising precomposition uses the factor edge
`T(-ν₊) → T(-μ₊)` with `-ν₊ + α_i = -μ₊`. Consequently its desired right
adjoint must come from the factor's **left** adjunction. Transporting the
factor right adjunction gives the opposite orientation. The parity of the
left cup and cap is `ipar D i λ = p(i)(h_i(λ)+1)` in `MoreGenerators.lean`.
The proposed correction shifts the lowering precomposition summand by this
parity. A proof must transport the signed triangle identities as well;
parity bookkeeping alone does not establish the adjunction.

## What the mate calculation now proves

Write `q = (-1)^p`. The raw mate is the specified cup–crossing–cap composite.
`rouquierMate_normalized_slide` proves that its multiple `-q • mate`
satisfies the normalized slide directly from the upward relation.
For chosen sector inclusions and projections, `mate_slide_projection`
transports the slide whenever the sector dots intertwine.

The two ordered finite-series theorems then solve the projected slides:

- invert the source probe dot and kill the target reservoir tail to obtain
  the coefficients `q^r` in C;
- invert the target probe dot and kill the source reservoir tail to obtain
  the coefficients `-q^(r+1)` in D.

`SuperRouquierLoc.MateProjectionFormula.of_coordinates` combines these
steps. Its independent hypotheses are the upward slide, four dot
intertwiners, two cap–cup factorizations, four ordered power-coordinate
identities, two probe-dot inverses and two reservoir nilpotence bounds.
It does **not** assume either the desired projection identity or inversion
of the coupled mate. The negative probe indices are integers.

## Exact remaining categorical work

1. Construct the shifted reverse factor adjunction for raising precomposition.
2. Construct the original-datum crossings, including equal-odd rational
   crossings and multicolour polynomial and braid relations. The disconnected
   product associator does not supply these relations.
3. Realize the sector inclusions/projections and prove all coordinate
   hypotheses of `MateProjectionFormula.of_coordinates` for these crossings.
4. Identify the all-height negative windows with the ordered dot-conjugation
   formulas. `RouquierDotConjugation` proves the underlying correction
   identities at every length, without dropping the cap–cup terms.
5. Put the resulting whole Schur feedback in a vanishing two-sided ideal
   filtration, then apply the associative inversion theorem.
6. Assemble the separated cover family back to the original datum.

`RouquierFeedbackIdeal` proves the algebraic implication in step 5: the nth
power of a matrix whose entries lie in filtration level one lies entrywise
in level n. A vanishing level kills the whole matrix, and
`isUnit_of_feedback_filtration` supplies the coupled block inverse. It does
not yet construct the filtration or prove membership for the categorical
feedback. Entrywise nilpotence is never used as a substitute.
