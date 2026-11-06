# Fixed-weight reservoir-vacuum detection

> The Nondegeneracy Conjecture in the research scope is proved in Lean (`nondegeneracy_of_symmetrizer`; see
> [STATUS](STATUS.md)). Steps described below as open, pending or conditional are either
> proved among that theorem's dependencies or belong to routes it does not use.

## Conditional Lean interface

`QuiverHecke.ReservoirVacuumEvaluation` records the extracted linear data of
a proposed fused action at **one prescribed external weight** `μ`. Its modules
are indexed by active upward words. There is no spectator word, and no
assertion that an upward action is faithful.

The data to be supplied by fusion and its comparison with the reservoir are:

- linear action maps on the presented `UpwardHom`, compatible with composition;
- cyclic vectors, and the source-placed categorical `betaSYM` action;
- a coefficient action `reservoir` on those same modules;
- a linear extraction into the connected `ELVRelationSpan` quotient on `t,t'`;
- its affine-coordinate law on a specified bounded coefficient/PBW window.

`NormalizedBubbleFormula` is **an explicit remaining categorical hypothesis**.
It identifies the action on each elementary generator `e_{n+1}` and on each
odd colour's own exterior generator. `normalized_bubbles` extends this formula
to all of `SYM`, using its algebra presentation. `odd_bubble_vacuum` identifies
the source-placed odd bubble with that colour's reservoir coefficient.
Neither theorem computes an inverse mate or constructs the categorical formula.

The coefficient action may incorporate the probe-series normalization. The
recovery map must then undo that normalization on its bounded window. It is
not required to induce an automorphism of a finite ELV quotient. In particular,
the affine-coordinate law is deliberately **bounded**, not an assertion that
an arbitrary triangular substitution preserves the top-coefficient relation.

## The two conditional deductions

`observe_source` uses composition to combine the normalized bubble law with
the affine-coordinate law, on the same cyclic vector. `observe_coefficient`
extends the resulting identity over the bounded extended PBW span. This is
the C2 joint coordinate identity, not two separate independence statements.
`vacuum_ne_zero_of_window` also proves that a nonzero vector in a sufficiently
large window forces the chosen vacuum to be nonzero; zero modules cannot
satisfy these coordinates on such a window.

`FusedFixedWeightFamily` asks for enough such windows at the same `μ`: for
each degree `d` and words `t,t'`, a window contains degree `d` and has a cutoff
lower bound `N` satisfying

```
d + 2 * t.length.choose 2 < N.
```

`vacuum_evaluations_jointly_detect` applies the existing bounded ELV separation
theorem to this identity. `upwardCoefficientMap_injective` is C3 at `μ`;
`upward_independence_of_fused_fixed_weight_families` supplies the global
`WeakMate.UpwardIndependence` consumer when these families are given for every
weight. Construction of the families, their nonzero vacua, and weight coverage
remain A2/A3 obligations. No instance of a fused family is claimed here.

This replaces `SpectatorEvaluation` **for the separated-sector route only**.
The earlier interface remains the consumer for a one-sector evaluation with
spectators. It still needs its additional joint-detection hypothesis. The new
estimate counts only the active strands, so the previously proved
`spectator_crossing_bound_obstruction` does not apply to it.

## Both cutoff parities

All bounded separation deductions accept arbitrary colourwise cutoffs.
`reservoir_parity_cutoffs_detect` explicitly proves separation along
`cutoff_m(i) = 2*m + ε(i)`. Setting `ε(i)` to either zero or one allows any
prescribed mixture of even and odd cutoffs, including adjacent odd colours.
This removes no categorical parity obligation: A0/A3 must still realize the
appropriate cutoffs at the given weight. No root-lattice cofinality is assumed.

## Cover levels and weight-lattice realization

`ReservoirWeights.level_difference`, `reservoir_parity`, and
`observation_bound` construct cofinal paired levels at any prescribed coroot
pairing `h`. Explicitly, the probe has level `2m + 2(-h_i).toNat`, and the
reservoir has level `2m + (h_i).toNat + (-h_i).toNat`. Their difference is
`h_i`, the probe is even, and the reservoir has parity `h_i mod 2`.
`odd_pairing_invariant` proves that signed root words cannot change that
parity at an odd colour.

These statements port the balancing arithmetic in the even
`Unfurling/GenericWeights.lean`. Its weights live on the **cover**, so its
pairing identity does not assert the existence of dominant weights in an
arbitrary original lattice `X`. `exists_weights_of_pairing_surjective`
realizes the levels by weights of literal difference `μ` when the joint
coroot map is surjective. This extra hypothesis is not part of `SKM.Datum`
and must not be added silently to the nondegeneracy conjecture. The
connected two-odd datum with coordinate coroots satisfies it.

`pairingExtension` adjoins independent coordinates, replacing `X` by
`X × (I → ℤ)` with coroot `h_i(ν,a)=h_i(ν)+a_i` and root `(α_i,0)`.
The Cartan matrix and parity are unchanged. `exists_extended_weights`
constructs paired weights of literal difference `(μ,0)` for every original
`μ`, without any lattice-richness assumption. This supplies arithmetic
coverage in an explicitly constructed larger lattice.

For example, on the root lattice of affine A1 with Cartan matrix
`[[2,-2],[-2,2]]`, the two coroot pairings sum to zero; no weight has both
pairings strictly positive. Thus arbitrary-lattice coverage must instead
use cover levels and a compatible relabelling of the action's external
weights. `restrictRouquierFamily` now constructs that restriction for the
super Rouquier factor interface, including its homogeneous local inverses,
in `ReservoirWeightRestriction.lean`. It does not construct a full
multicolour action or a fused family, so `FusedFixedWeightFamily.covers`
remains a categorical obligation.

## Bounded coordinates on the connected regular quotient

Over a field, `QuiverHecke.reservoirWindowCoordinates` in
`ReservoirCoordinates.lean` constructs a total linear extraction from the
connected reservoir quotient to its bounded joint coefficient/PBW window.
`reservoirWindowCoordinates_apply` proves recovery whenever
`d + 2 * t.length.choose 2 < N` and all cutoffs are at least `N`.
The construction splits the already-proved bounded injection as a linear
map; it does not require a cyclotomic ideal to be stable under normalization.
The whole joint window is recovered, including crossings with products of
distinct exterior generators.

`exists_bounded_reservoir_extraction` applies this to **any** linear source
coordinate map. Its extension off the bounded image is noncanonical. It
establishes the existence of a total extraction on the regular quotient,
not the `affine_coordinates` identity on the still-unconstructed fused
vacuum. The remaining comparison must identify the fused word module,
its cyclic vector, and its dot/crossing/coefficient operators with these
connected coordinates. A normalization formula and its degree bound must
still be proved for that comparison.

## Regular cyclic action and source-order normalization

`ReservoirRegular.lean` descends actual postcomposition to the connected
ELV quotient. `elvRelationSpan_postcomp` proves stability of the defining
relation span. `reservoirPostcomp_generator` evaluates a morphism on the
identity class, and `reservoirRegular_injective_on_window` combines this
cyclic evaluation with bounded separation. These operators use the signed
coefficient category, not an unsigned tensor-product multiplication.

There is a necessary source-order correction. For homogeneous coefficient
`a` and affine morphism `f`, applying `a` at the source and then `f` gives
`(-1)^(|a||f|) [a ⊗ f]`, not `[a ⊗ f]`. In
`ReservoirSourceCoordinates.lean`, `reservoirSourceOrder` is the corresponding
diagonal involution of the joint PBW basis. It preserves every bounded
window and is the identity on the zero window.
`reservoirSourceOrder_source` proves the formula for arbitrary, not just
homogeneous, inputs. `exists_reservoir_source_coordinates` constructs a
single linear extraction undoing this sign for every coefficient/affine
input in the window. It does not assert that the involution descends to an
automorphism of the ELV quotient.

A regular-window coverage module (`ReservoirCoverage`) proved joint
detection along balanced regular levels for the connected regular quotient.
No consumer used it and it was removed; it did not identify that quotient with
the fused word module, which remains the open comparison.

## Algebraic normalization, and its remaining gap

`SKM.reservoirDeconvolution` is a recursively defined finite triangular inverse
for ordered multiplication by a series with constant coefficient one.
`reservoirDeconvolution_convolution` proves the inverse identity over any ring,
including a noncommutative ring with zero divisors.
`reservoirDeconvolution_eq_upto` proves locality in a finite coefficient window;
`reservoir_coefficients_recovered` consumes a convolution formula known only
on that window. `reservoir_exterior_recovered` removes a unit normalization
without inverting an exterior element.

**Proposed categorical application, still open:** compute the fused normalized
bubble series from the actual inverse mate, identify the probe factor and the
odd unit signs, and show that the reservoir affine-coordinate extraction
implements these finite inverse substitutions. The Lean recursion supplies
the algebraic inverse, not that identification or an automorphism of `SYM`.
In particular, these results do not yet prove a multicolour categorical bubble
evaluation theorem without a formula hypothesis.

The super input is now `SKM.SuperRouquierLoc` and
`RouquierBoundary.Coefficients.ofVacuumInverse`, not a second local-action
interface. The inverse gives the normalized finite Kronecker window
`Coefficients.cup_cap`. It does **not** identify the dot's deformed
cyclotomic polynomial or its exterior coefficient. The even
`VacuumRouqBubbles.lean` additionally proves a concrete block comparison
for the mate and dot operators before applying the coefficient calculation
in `VacuumBubbles.lean`. The super analogue still needs that comparison
with the connected reservoir module, including the odd coefficient action
and probe normalization. `NormalizedBubbleFormula` is now derived from the
mate projection formula, under the action and fusion-inversion outputs listed
in the next section.

## Fused vacua and sector bubbles (removed)

An interface route (`ReservoirFusedVacuum`, `ReservoirFusedBubbles`,
`ReservoirFusedDetection`, `ReservoirFusedSectors`, with the concrete tests
`ReservoirVacuumExamples`) derived upward independence from an assumed fused
vacuum action with bubble sectors. No instance of that action was ever
constructed, no consumer used these modules, and they were removed. The
missing input is unchanged: the vacuum word modules of the fused action with
their regular identification, and the identification of the capped mate
composite with the fused bubble of each generator.
