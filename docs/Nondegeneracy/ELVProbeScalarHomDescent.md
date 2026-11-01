# Literal ordinary Hom descent for scalar-evaluated old modules

`ELVProbeScalarHomDescent.lean` proves that the scalar image of the
untruncated full old cyclotomic ideal equals the entire existing ordinary
`cycHom` ideal. The reverse inclusion lifts arbitrary affine contexts with
coefficient one and uses the already proved exact first-relation image.

Together with scalar representation factorization, this proves actual
scalar-evaluated old modules annihilate every ordinary relation. The
literal quotient linear map `probeOrdinaryModuleHom` is constructed, and
its composition with `elvProbeOldHom` is proved to be the original old
arrow action. No action on intermediate words outside the fixed content
is needed: their lifted relation lies in the original old ideal before
the endpoint module is applied.

Strict local producer and all closed consumers pass; all 15 owned
declarations pass the axiom audit. Mixed-parity fixtures check the exact
ideal image, elementary coefficient -3, exterior coefficient zero and
the prescribed actual first-dot relation. Full CI remains the
integration gate.

The ordinary word-category functor packaging and the coend comparison
with existing height induction remain separate. No flatness or tensor
kernel hypothesis is imposed, and no weighted coefficient truncation
is specialized.
