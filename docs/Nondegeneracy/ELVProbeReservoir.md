# The OLD probe and ELV reservoir factors

SwappedActionAssembly F1–F2 requires a probe with invertible dots and a
reservoir on the same presentation parameters. `elvProbeReservoir` pairs the full scalar-evaluated OLD probe with the specified
truncated ELV reservoir. Both act with `parameterTwist D Sc`, and both
multicolour records have presentation parameters `Sc`.

The probe's shifted left adjunctions are the existing
`RouquierFamily.leftAdjoints` construction. The chosen factor families
and this adjunction datum are retained definitionally. The stated cutoff
pairings identify their actual highest weights. At empty sector the
probe weight is `ΛP` and the reservoir weight is `-ΛR`; the Hom source
uses the probe's negative weight as specified by `ProbeReservoir.H`.

For finite colours, `elvProbeReservoir_dot_isUnit` has the exact
whole-probe-dot form required by the mixed denominator constructions. This constructor
does not assume global reservoir-dot nilpotence. The proved reservoir
bounds in `ELVWeightDenominatorUnits` and the shifted variants are
contentwise and are the relevant inputs for the mixed denominators.

The producer and paired concrete consumer pass scoped checks with the pinned toolchain, warnings as errors and both compatibility settings. The consumer audits all nine owned declarations against the repository axiom allowlist. It constructs the factor pair on both mixed even/odd and connected two-odd symmetrizable data, proves both cutoff pairings, identifies the empty-sector weights and supplies nonzero vacuum append vectors for the acting probe parameters.
This factor constructor alone supplies no crossing coefficients,
residual coefficient-image witnesses, corner maps or vacuum observation.
