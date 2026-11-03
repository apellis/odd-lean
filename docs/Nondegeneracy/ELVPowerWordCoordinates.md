# Actual regular-power word coordinates

`ELVPowerWordCoordinates.lean` constructs coordinates for the actual regular
A/T word values of `SwappedVacuumCoordinates.md` §§2–3. All coefficients,
including independent exterior products, remain in the original full ELV
coefficient algebra and its literal elementary-power quotient.

The canonical coefficient-insertion functor at an old word ν sends a to
`coefficientEndomorphism ν a`. Its empty case is literally the chosen empty
coefficient embedding. Actual right append preserves this functor.
`powerWordModule` is its actual balanced induction of the regular A/T module;
`powerWordModule_nil` is the chosen vacuum and `powerWordAppendIso` uses the
existing selected induction-composition comparison. This relates the word
values to successive actual append inductions without assumed regularity.

The actual coend generator `powerWordGenerator` is h tensor 1. It is
surjective, and its kernel is computed from the original balance relations.
The proof constructs a contraction by descending coefficients through A/T;
balancing uses the explicit noncommutative order f*a. No flatness premise or
commutativity of A/T is used.

`powerWordRelationSpan_eq_elementaryPowerImage` identifies this kernel with
the independently defined actual two-sided elementary-power Hom image.
Only the proved even elementary-power slide is used to move its generators
between word contexts. Arbitrary full coefficient multipliers are retained.

`powerWordModule_property` and `powerWordObject` put every word value in the
literal coefficient-power module category. `powerWordSourceMap_ker` then
identifies its native source kernel exactly with `ELVRelationSpan` plus the
two-sided span of the same literal source powers.

The paired consumer imports this producer and `HalfTurn/PowerWordCoordinates`.
At the asymmetric odd Cartan datum, cutoff eight and power exponent three,
it proves that an occupied two-strand joint PBW coordinate containing BOTH
independent odd exterior generators survives in the actual word value.
It also tests the empty vacuum, actual append comparison, power-module
membership, full source kernel, and prescribed reservoir schedule.

Verification: strict pinned checks passed for both producers and the paired
consumer. All 60 declarations owned by this producer and all 9 owned by the
half-turn coordinate producer are audited, including private/generated
ones, against `propext`, `Classical.choice`, and `Quot.sound`.

The signed Hom/Yoneda chart and comparison of the chosen SKM action's dot
and crossing evaluations with these native coordinates remain subsequent
work. The source-coordinate kernel theorem does not assume that evaluation
identity or assert nondegeneracy.
