# Detection with spectator strands

## Fixed-weight evaluation interface

`SpectatorImage` and `SpectatorEvaluation` describe the regular-projective
fragment of a cyclotomic action. They do not construct that action or the
fusion of two weight sectors. In the theorem graph of
[GeneralRoute.md](GeneralRoute.md), they specify one possible target for C2;
they do not discharge C1 or C2.

The external weight `μ` is fixed. An individual test specifies a spectator
word `s`, a base weight `λ` with `wt(λ,s)=μ`, and a colour-dependent cutoff.
The source and target quotient spaces have words `s ++ t` and `s ++ t'`.
Thus their cyclotomic content contains the spectators. The quotient is exactly
`ELVRelationSpan`, not an unspecified representation satisfying a subset of
its relations. No dominance or availability of these tests is asserted.

The affine image is the explicitly defined `spectatorAffine`: whisker the
affine morphism by the identity on `s`, then extend coefficients. A test also
specifies linear lifts of its bubble operators into the coefficient-extended
endomorphism space of `s ++ t`. Lifts need not preserve multiplication before
passing to the quotient. Their identification with categorical bubbles is
part of the separate `product_law` obligation.

`SpectatorImage.image` combines the bubble lift and the specified affine
operator using composition in the signed coefficient category. In particular,
it does not replace this product by an unsigned tensor product. The action
component takes an upward 2-morphism to a linear map from the source quotient
endomorphism module to the quotient Hom module. Evaluation at the cyclic
identity gives `observe`. The product law implies

```
observe (upwardCoefficientMap f) = quotientImage f.
```

`upwardCoefficientMap_injective_of_spectators` then consumes *joint* detection
of the explicit `quotientImage` family. `upward_independence_of_spectators`
connects this to `WeakMate.UpwardIndependence`. These are conditional consumer
theorems, not a construction of a detecting family. Unlike the older
`FiniteUpwardObservations`, no map recovering a quotient on the active words
alone is requested.

The even comparison separates the same jobs: `RouqFamily.upEval` evaluates
2-morphisms, `CyclotomicAction.theta` takes cyclic coordinates,
`unfurledEvalOfVacuum` consumes the evaluated bubble law, and
`GenericFields.bubbleEval_indep` establishes independence of the specified
bubble parameters. The last of these is not an independence theorem for
exterior coefficients in an ordinary field.

## Separation theorems and remaining obstruction

The following are Lean theorems in `SpectatorSeparation`:

- `cofinal_elv_quotients_with_spectators_detect` separates the full augmented
  Hom space for fixed `s,t,t'` and any colourwise cofinal cutoff family. In
  particular the cutoffs need not be even. A concrete two-odd-colour example
  retains an exterior-product basis vector with a nonempty spectator word.
- `spectator_quotientImage_ne_zero` gives the degree criterion for a specified
  joint image. `spectator_images_detect_of_bounds` assembles it for a moving
  family, provided each nonzero input has a nonzero joint image and a suitable
  bound at the **same** family index.
- `spectator_crossing_bound_obstruction` proves that `N ≤ 2n` and `n ≥ 3`
  preclude the bound below, for every nonnegative degree `d`. It is not a
  nonvanishing or vanishing theorem for the quotient.

**Proposed fixed-weight analysis.** The existing
ELV estimate for a bounded vector of degree `d` on `n` strands requires

```
d + 2 * choose(n, 2) < N.
```

For spectators one must use `n = length(s ++ t)`, not `length(t)`.
Holding `s` fixed and allowing arbitrarily large cutoffs separates the whole
augmented Hom space. But in a lowest-weight test at fixed `μ`, changing the
cutoff can change the lowest weight and therefore the required spectator
content. The quantifiers cannot be interchanged.

Already in the rank-one weight arithmetic with coroot pairing two, take
external weight zero and lowest-weight height `2m`. Reaching zero uses `m`
raising strands. Thus the cutoff is `2m` while the total number of strands
is at least `m`. For `m ≥ 3`, even the degree-zero version of the displayed
estimate cannot apply. This does **not** prove that the evaluated vector
vanishes: the estimate may be far from sharp. It does show why the existing
vacuum proof cannot simply be reused with growing spectators.

The next mathematical input must be either a sharper theorem for the
particular spectator corner, a proved extraction to a reservoir vacuum with
bounded active content, or a fixed-weight fused test object for which the
required content and cutoff bounds hold. The proposed fused construction in
GeneralRoute is not supplied by the interface above.

No bubble formula at arbitrary spectator content is established here.
Even after identifying independent bubble images, one must prove that their
products with the affine operators survive. In particular the connected
two-colour example in HANDOFF, where the exterior product survives but its
product with a reverse crossing does not, is not excluded by separate
bubble and affine independence assertions.
