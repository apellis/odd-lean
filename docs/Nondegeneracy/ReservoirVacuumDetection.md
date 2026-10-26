# Fixed-weight reservoir-vacuum detection

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

`ReservoirCoverage.lean` supplies the everywhere-defined regular window
`regularVacuumWindow m n = 2*m - 2*choose(n,2) - 1` (natural subtraction).
`regularVacuumWindow_coordinates` constructs normalized source-order
coordinates for every `m` and every active word. At small cutoffs the window
is zero, and the identity extraction suffices; positive windows use C0.
`regularVacuumWindow_covers` gives cofinal coverage for these actual regular
windows. `exists_regular_vacuum_window` simultaneously realizes extended
weights of literal difference `(μ,0)` and an injective cyclic regular window.
`balanced_regular_vacuums_detect` proves joint detection along these levels.

This removes the source-order normalization and window-selection problems
**for the connected regular quotient**. It does not identify that quotient
with the fused word module. The comparison must still construct the fused
vacuum, its word modules, and their affine and coefficient operators. The
scalar-polynomial quotient action and its height-one vacuum map do not yet
supply the full exterior-coefficient vacuum tower or its comparison with these
connected quotient modules. In particular,
these results do not by themselves inhabit `FusedFixedWeightFamily`.

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

## Fused vacua, sector bubbles and the restated detection theorem

`ReservoirFusedVacuum.lean` (porting `CyclotomicAction/VacuumProduct.lean` and
`Unfurling/GenericVacuumWordCoordinates.lean`). `FusedVacuumWords` is an
upward action evaluated on the word modules of one vacuum.
`RegularVacuumIdentification` identifies these with the connected regular
modules: coordinates `coord s t : V t → e_t R^Λ e_s` sending the vacuum to the
regular generator, affine operators to postcomposition and the reservoir
coefficient action to source-placed coefficients. No injectivity is assumed.
`FusedVacuumWords.evaluation` builds a `ReservoirVacuumEvaluation` whose
`affine_coordinates` is proved from C0 on the regular window, and
`FusedRegularVacuumFamily.toFamily` proves the categorical `covers` field from
`regularVacuumWindow_covers`.

`ReservoirFusedBubbles.lean` (porting `Unfurling/VacuumRouqBubbles.lean`,
`GenericVacuumBubbles.lean`, `GenericKLBubbles.lean`). With `q = (-1)^{p}`,
the first identity of `SuperRouquierLoc.MateProjectionFormula`, capped by a
probe cup `κ : 1 → X_B` and a reservoir cap `ℓ : Y_A → 1`, gives
(`mate_projection_sector_bubble`)

    κ (−q·σ)_{B→A} ℓ = Σ_{r<n_C} q^r (κ v_{B,−r−1}) ∘ (u_{A,r} ℓ),

the probe coefficient acting first. `VacuumBubbleSector` evaluates this on the
word modules. If the capped composite is the fused bubble of a generator `g`
(fusion inversion), the probe coefficients act by scalars `c_r` and the
reservoir coefficients by `res_r` (action), and `Σ q^r c_r res_r = g`, then
`bubbles_eq` gives `bubbles(g) = reservoir(g)`. `fused_bubbles_eq_reservoir`
extends this to all of `SYM` and `fused_odd_bubble` identifies the odd bubble
with the reservoir's exterior generator. `sector_normalize_deconvolution`
shows that a scalar probe series with constant term one always admits this
normalization, with `c_r = q^r P_r` and deconvolved reservoir coefficients.

`ReservoirFusedDetection.lean`. `FusedVacuumAction` collects the fused vacuum
family on the balanced levels `reservoirLevel (⟨h_j, μ⟩) m` together with its
bubble sectors; `upward_independence_of_fused_vacuum_actions` assumes these
and the mate projection formula for every sector, and proves
`WeakMate.UpwardIndependence`. The two-odd consumer
`scripts/NonVacuity/ReservoirFusedDetection.lean` instantiates the headline at
the connected two-odd datum and checks the normalization with a nontrivial
probe series and a product of both exterior generators.

`ReservoirFusedSectors.lean` builds the sectors from reservoir and probe
summands (`SKM.SourceSector`, `SKM.TargetSector`). With the upward slide of
the coupled crossing, inverses of the probe dots and nilpotence of the
reservoir dots, F's `MateProjectionFormula.of_sectors` proves the projection
formula (`VacuumSectorBubble.toSector_mateProjection`); the coordinates are
the dotted reservoir cups and the probe caps with powers of the inverse probe
dot. `upward_independence_of_fused_sector_actions` has no mate projection
hypothesis.

**Remaining obligations.** No instance of `FusedVacuumAction` or
`FusedSectorAction` is constructed. Their fields are exactly: (A0/A1) the
vacuum word modules of the fused action, their regular identification, the
sector summands with the crossing slide, probe inverses and reservoir
nilpotence, the scalar action of the probe coefficients and the reservoir
coefficient values; (A2) the identification of the capped mate composite with
the fused SKM bubble of each generator, including the degree bookkeeping of
the dotted cup and cap. The regular-module side (C0,
coordinates, covers) and the passage from these inputs to upward
independence are proved.

## Connected tests

`ReservoirVacuumExamples` uses the symmetric Cartan matrix with diagonal two
and off-diagonal minus two, both colours odd, over the rationals. It checks
mixed-parity separation, coefficient-series recovery in the common `SYM`
algebra with the product of distinct exterior generators retained, and
injectivity of the entire degree-two crossing window at cutoff five. In that
window `crossing_two_exterior_ne_zero` exhibits a specific nonzero canonical
crossing vector carrying the product of the two distinct exterior generators.
These are concrete algebraic tests, not a construction of the fused family.
The small-cutoff obstruction involving a reverse crossing times two exterior
generators is respected: the tested cutoff is above the bounded separation
threshold, and no tensor product of rank-one representations is used.
