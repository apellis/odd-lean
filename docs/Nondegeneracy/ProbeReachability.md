# Parity-compatible probe weights and the regular vacuum

## Statement and status

The weight-arithmetic part of A3 is already proved. For every weight `μ` of
an arbitrary `SKM.Datum D`, the pairing extension has dominant probe and
reservoir weights with difference exactly `(μ,0)`, even probe levels, and
cofinal reservoir levels of the parity required by `μ`. This does not
construct an SKM action or identify its vacuum word modules. Those are the
remaining categorical obligations; parity-compatible reachability is not
an additional obstruction.

The distinction is important for general symmetrizable data. No argument
below assumes finite type, independent roots, surjective original coroot
coordinates, or cofinal dominant weights in an original root-lattice coset.
The arithmetic and regular-coordinate declarations do not even require a
finite colour set. Words and individual observations have finite support.

## The source constraint and its specialization

Kang–Kashiwara–Oh, *Supercategorification of quantum Kac–Moody algebras*,
arXiv:1206.5933v2, §7.1, prescribes a monic cyclotomic polynomial of degree
`⟨h_i,Λ⟩`, with the coefficient indexed by `k` zero for odd `k` at an odd
colour. In particular, an odd-degree polynomial of that form has zero
constant term. An everywhere invertible-dot probe built from the whole
one-strand cyclotomic quotient therefore uses even degrees at odd colours.
This is a constraint on the probe, not on the external weight. Restricting
to a nonzero spectral summand would be a different construction, and is
not needed for the weight arithmetic here.

Put `h_i = D.h i μ`, and write `h_i⁺ = max(h_i,0)` and
`h_i⁻ = max(-h_i,0)`. The existing definitions are

```
P_i(m) = 2m + 2h_i⁻           (probeLevel)
R_i(m) = 2m + h_i⁺ + h_i⁻     (reservoirLevel).
```

`ReservoirWeights.level_difference`, `probe_even`, `reservoir_parity` and
`levels_cofinal` prove, respectively,

```
R_i(m) - P_i(m) = h_i,
P_i(m) is even,
R_i(m) mod 2 = h_i mod 2,
∀ N, ∃ m, ∀ i, N ≤ P_i(m) and N ≤ R_i(m).
```

Thus take probe polynomial `(u²-a_i)^(P_i(m)/2)` at an odd colour, with
`a_i` a unit; its constant coefficient is a unit. The connected reservoir
has degree `R_i(m)`, which may be odd. This specialization is only a choice
of degrees and a candidate probe polynomial; it does not prove the
all-content probe action or the odd-coefficient reservoir deformation.
The latter is outside the even-coefficient restriction just recalled.
In particular, at an odd colour with even `h_i`, every `R_i(m)` in this
schedule is even. Thus this schedule does not avoid the even-cutoff
phenomenon discussed in [CyclotomicDeformationProof.md](CyclotomicDeformationProof.md):
the full ELV coefficient ring has the relation `d_i χ_(i,m)=0` at an even
cutoff. The exact ELV quotient used below must be retained; unrestricted
exterior-coefficient flatness is not a consequence of the weight choice.
Nor does weight coverage supply the residual identity-summand matrix
required for fusion inversion in [FusionReservoirLemma.md](FusionReservoirLemma.md).

The sign convention here is **reservoir minus probe**. Reversing the order
of the two factors replaces `h` by `-h`; one must make this replacement
when comparing conventions for the Hom construction. The invariant is the
literal external weight, not an informal designation of a positive sector.

## Original weights, extended weights, and cover labels

The even reference `GenericWeights.sum_level_difference` sums multiplicities
over disjoint spectral labels. `vacuum_finsum_base` then computes the base
coroot coordinate of the cover weight. Such a coordinate equality alone
would not identify an arbitrary original weight: coroots can have a common
kernel.

Here `ReservoirWeights.pairingExtension D` instead has weight group

```
X̂ = X × (I → ℤ),
α̂_i = (α_i,0),       ĥ_i(x,z) = h_i(x) + z_i.
```

It retains the original colour set, Cartan matrix and parity. It is not
itself a spectral unfurling or a fusion of two colour copies. In particular,
symmetrizability is preserved because the Cartan matrix is unchanged.

There is an explicit choice

```
μp = (0, P(m)),       μm = (μ, P(m)),
μm - μp = (μ,0),      ĥ_i(μp) = P_i(m),     ĥ_i(μm) = R_i(m).
```

The theorem `ReservoirWeights.exists_extended_weights D μ m` gives precisely
these conclusions (through pairing surjectivity of the extension). The
original `X` coordinate is retained, even in the kernel of all coroots.
`exists_weights_of_pairing_surjective` is a separate theorem with an extra
hypothesis; that hypothesis is **not** required of `D` here.

The embedding `j(μ)=(μ,0)` preserves roots and pairings. The proved
`extension_edge` transports each root edge, and `restrictRouquierFamily`
restricts a supplied super Rouquier family to `D`, retaining dots,
crossings, adjunctions and local inverse data. Its object at `μ` is literally
the extended family's object at `(μ,0)` (`restrictRouquierFamily_obj`).
This is a restriction theorem for the **RouquierFamily interface**, not a
construction of that family, a full multicolour presentation comparison,
or a theorem that the SKM presentation embedding is faithful.

At the level of presentation labels, every signed word remains in `j(X)`:
its successive weights are obtained by adding or subtracting `(α_i,0)`.
Pairings and Cartan parameters at those weights are unchanged. Thus the
required full-action restriction must map the original generators to the
same extended generators on these weights and verify the original
relations there. It needs a well-defined interpretation, not faithfulness
of a weight-lattice inclusion as an additional assumption. The available
`restrictRouquierFamily` proves only the stated part of this transport.

`odd_pairing_invariant` moreover proves that adding any signed root word
preserves each odd coroot pairing modulo two. Intermediate finite contents
therefore introduce no new parity class to solve. This does not assert
that every such content has a nonzero cyclotomic module.

## The existing regular-window theorem

Specialize `exists_regular_vacuum_window D Sc μ t t' d` to the desired
original weight and finite pair of words. It supplies `m,N,μp,μm` with the
literal weight difference above, both cutoff lower bounds, and

```
d + 2 * choose(length t,2) < N.
```

Its final conclusion is injectivity on `ExtendedAtMost D Sc t t' d` of
postcomposition evaluated on the regular generator in the connected ELV
quotient at cutoff `reservoirLevel (fun i => D.h i μ) m`. Together with
`probe_even`, this is exactly the parity-compatible algebraic window
specialization needed in A3. It works over the `CommRing` and `Scalars`
hypotheses of the theorem, without a highest-weight dominance assumption
on the original lattice. `balanced_regular_vacuums_detect` gives joint
detection over all `m`.

For finitely many observations, choose a common bound on their degrees and
lengths and increase the common cutoff. No finite-type argument or bound
on spectator content is used. For infinitely many colours the coordinate
function `P(m)` need not have finite support; it is a weight in the stated
product extension. The words and tested coefficient expressions still
have finite support. This arithmetic fact must not be confused with a
constructed infinite-colour categorical action.

## Exact remaining regular-vacuum obligation

For each original `μ` and each `m`, construct the word modules `W.V t` of
the separated, fused action at `j(μ)`, then restricted to `μ`. Supply the
actual upward action, cyclic vectors and source-placed bubble action as a
`FusedVacuumWords D Sc cs μ`. Next construct

```
RegularVacuumIdentification W (reservoirLevel (fun i => D.h i μ) m).
```

This structure demands linear maps `coord s t` from `W.V t` to the exact
connected ELV quotient from `s` to `t`, and three concrete identities:

1. `coord t t (W.vacuum t)` is the quotient class of the identity.
2. Under `coord`, the affine action `W.act ((alpha D Sc μ).map f)` is
   postcomposition by `sourceCoefficientHom D Sc 1 f`.
3. A constructed reservoir coefficient action on `W.V t` becomes
   postcomposition by `sourceCoefficientHom D Sc a (𝟙 _)`.

The operators and quotient here use the signed coefficient composition;
an unsigned tensor-product identification does not suffice. Neither an
abstract regular module nor a cyclic vector in an unrelated representation
supplies these identities. No injectivity or isomorphism of `coord` is
required by this interface. Its missing construction cannot be replaced
by assuming that these very coordinate identities hold.

Once these data exist, `FusedVacuumWords.evaluation` proves the bounded
affine-coordinate law, and `FusedRegularVacuumFamily.toFamily` proves the
categorical `covers` field from `regularVacuumWindow_covers`. The latter
still requires the normalized bubble formula. Over a field the recovery
map also corrects source-order Koszul signs, via
`regularVacuumWindow_coordinates`; it is not an assertion that the sign
involution preserves the ELV ideal.

Finally, `RouquierCoupledSectors.FusedCoupledAction` is not an existence
theorem (its declaration is in namespace `OddMath.QuiverHecke`). Its
`family` field already contains the regular identifications. Its `sectors`
field still requires, for every coefficient generator, `CoupledSectorBubble`
data including `fusedBlock`, `probe`, `reservoirValue` and `normalize`.
`toVacuumSectorBubble` constructs the structural sector fields from supplied
coupled factors; it does not construct those vacuum values or identify the
fused inverse block with the presentation bubble. These remain separate
from the regular-vacuum comparison.

## Closed and open

| Assertion | Status |
|---|---|
| Even probes and cofinal parity-compatible reservoir levels for every `μ` | Proved in `ReservoirWeights` |
| Literal weight difference in the extension, including invisible coroot-kernel coordinates | Proved by `exists_extended_weights` |
| Restriction of a supplied super Rouquier factor family to every original weight | Proved by `restrictRouquierFamily` |
| Joint regular ELV detection with the same balanced cutoffs | Proved in `ReservoirCoverage` |
| Full fused action and its interpretation on the original presentation | Open; not supplied by factor-family restriction |
| Fused vacuum word modules and the three regular coordinate identities | Open construction of `RegularVacuumIdentification` |
| Actual normalized probe/reservoir vacuum values and fused bubble block | Open action comparisons, not weight arithmetic |

Consequently A3 must not be marked entirely closed. Its parity-compatible
weight choice and algebraic window coverage are closed; the categorical
regular-vacuum and bubble identifications are not.
