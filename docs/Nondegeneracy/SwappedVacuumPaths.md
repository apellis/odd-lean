# Upward paths at the probe vacuum

SwappedActionAssembly §6 and SwappedVacuumCoordinates §2 require that the
vacuum's upward words use only reservoir induction. The combinatorial
source is `OddMath/QuiverHecke/SwappedAssembly/VacuumPaths.lean`.

`SPath.probe_le_of_upward` states that the probe content cannot decrease
along an upward path. If the terminal probe content is zero,
`side_eq_false_of_upward_probe_zero` forces the first summand to be the
reservoir summand. Induction yields
`subsingleton_of_upward_probe_zero` for arbitrary word lengths, repeated
colours and external weight labels. `sum_of_upward_probe_zero` reduces the
finite middle-path sum to a supplied occupied path, retaining arbitrary
coefficient values.

The paired consumer constructs a length-three repeated-colour reservoir
path from positive reservoir content to the empty sector and tests a
nonzero finite-sum value. The producer and paired consumer pass strict
scoped checks with the pinned toolchain, warnings as errors and both
compatibility settings. The consumer audits all five owned declarations.
Full integration verification remains separate.

The next attachment identifies the corresponding component of the
literal swapped `layerMap` with the chosen word-module operators, using
the existing contextual dot and crossing comparisons. Path uniqueness
alone does not construct that evaluation or a nondegeneracy observation.
