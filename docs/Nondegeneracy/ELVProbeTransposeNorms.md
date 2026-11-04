# Transposed source norms for the OLD probe and ELV reservoir

The swapping block in SwappedActionAssembly F2–F3 and SwappedHomInversion
§2 requires three literal source norm units. The target mixed denominator
units alone do not provide this input.

`CyclotomicAction/ELVProbeTransposeNorms.lean` specializes the existing
`ELVMixedSourceNorms` and `ELVMixedSourceOddNorms` to the prescribed
`elvProbeReservoir`. Its `ELVProbeCrossTransposeNormUnits` supplies
`ProbeReservoir.CrossTransposeNormUnits`: the even source dot difference,
the odd square difference, and the odd square sum. The input probe dot is
the actual `P.T.dot`, whose unit theorem is already checked. The outer
operator is the actual reservoir right transpose under `P.W.adj`.
Arbitrary surrounding Hom functors and their content parity shift remain
unchanged. The symmetrizer and homogeneous parameter hypotheses are the
ones of the existing contentwise reservoir bound.

Those source norm inverses were assembled contentwise. The specialization
introduces no common nilpotence exponent over an original-weight fibre.
`elvProbeSwappingInvertible` combines this record with the constructed
mixed denominator units and the chosen coefficient's inverse identities,
using `ProbeReservoir.swappingInvertible_of_units`. It supplies every
off-central swapping entry for that coefficient. Central block
invertibility remains a separate input to the augmented matrix theorem.

The paired consumer uses the mixed-parity symmetrizable rational datum
with unequal symmetrizer entries and the existing all-odd asymmetric
datum. It exercises all three source norm fields, the actual probe dot
unit, the nontrivial Hom parity shift, and the complete swapping
invertibility statement. The probe append vectors are proved nonzero at
both colours; no norm-unit or inverse-comparison hypothesis is supplied
by the consumer.

The two source-dot operators in `RouquierHomDistinctMixedPostDotsIso`
are definitions with the same literal whiskering bodies. Keeping these
heads available makes the family attachment compare the specified source
operators directly. The existing power identities unfold them explicitly.

The producer and paired consumer pass the strict pinned Lean checks. The
consumer audits all 38 declarations owned by the wrapper, its two native
source-norm modules, and the mixed-source operator module; only the
standard allowed axioms occur.
