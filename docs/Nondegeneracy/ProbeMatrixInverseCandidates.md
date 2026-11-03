# Concrete scalar conjugates of the given old matrix inverses

Source: DeformedMatrixComparison (4), (5).

`probeTransportedUnitMatrixIso` takes exactly the given global
`TensorMatrixCoordinates.moduleUnitMatrixIso` on
M=Ind(oldContentInclusion) N, under its actual nonnegative Cartan-height
hypothesis. It conjugates that isomorphism through the genuine content33
finite/E/F charts and scalar65 finite/E/F charts.
`probeTransportedCapMatrixIso` does the same with the given old cap inverse
under its actual nonpositive-height hypothesis. Both constructions retain
the original given inverse through the same reversed charts; there is no
assumed isomorphism or replacement invertibility hypothesis.

Strict producer and paired consumer checks pass. The consumer uses mixed
regular scalar modules, both moving colours, actual positive and negative
height inequalities, zero and positive cap counts, and both inverse laws.
It checks the empty predecessor ν=[] explicitly as output[i]. All 56 owned
declarations pass the repository axiom allowlist audit.

The forward-map attachment is now supplied by
`ELVProbeMatrixInverse.probeTransportedUnitMatrixIso_hom` and
`probeTransportedCapMatrixIso_hom`. The relative-content-to-global and
scalar whole finite matrix squares identify both existing conjugates with
the independently prescribed components; no compatibility premise is used.
The companion note `ProbeMatrixInverse.md` gives the argument and checked
consumer scope.

Output content of these constructors is i::ν. Genuine empty output and
absent-i output are handled separately by `ELVProbeMissingColourMatrix`;
the ν=[] consumer here denotes output[i]. The attachment retains the
normalized old kernel cap formula and its full output parity action.
