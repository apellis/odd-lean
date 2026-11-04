# The corrected braid field of the probe Rouquier data

The source target is Brundan–Ellis (1.9), the corrected braid with repeated
outer colour and distinct middle colour. The declaration
`probeOldRouquierData_braidEq` in
`OddMath/QuiverHecke/CyclotomicAction/ELVProbeWeightMixedBraidField.lean`
identifies the whole-weight polynomial relation with the exact
`rouquierMixedBraidEquation` of the independently selected
`probeOldRouquierData`.

For arbitrary colours `i ≠ j` and the seven compatible weight equalities,
the acting data use `parameterTwist D Sc` while the relation uses `Sc`.
The signed dots and negative equal-colour crossings are the prescribed
ones. The statement adds no local inverse or polynomial-identity assumption.
Its proof consumes `probeOldActionCross_mixedBraid`, so it includes both
supported predecessor blocks and absent coordinates.

The conversion is proved first for an arbitrary Rouquier generator record.
The three signed dot positions give the ordered correction polynomial;
the generic polynomial-to-dotted theorem expands it into the two finite
sums in the literal field. The generator-record projections are decoded
before substituting the selected weight functors. At the specialization,
only the named crossing and dot positions are expanded. This leaves the
chosen action unchanged and avoids expanding its underlying coends.

The paired consumer uses the occupied two-colour word `[false, true]`
for the mixed even/odd datum and the connected two-odd datum with Cartan
exponents 2 and 4, in both orientations. It supplies the seven weight
identities and proves distinctness, occupancy, parity, symmetrizability
and homogeneity. A mixed homogeneous interior coefficient equal to 3
is also tested in both orientations; its acting coefficient is −3.
Nonzero vacuum append vectors for the acting twisted parameter families and an absent-source weight are included.
The producer and paired consumer pass scoped checks with the pinned toolchain, warnings as errors and both compatibility settings. The consumer audits all 53 declarations owned by the producer against the permitted axioms `propext`, `Classical.choice` and `Quot.sound`.

This conversion supplies the corrected-braid obligation for the selected
multicolour data. It does not supply the local rank-one inverse records
or the remaining nondegeneracy argument.
