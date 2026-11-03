# Two-step OLD probe induction at every original weight

`probeOldBlockPairInd` retains both actual block appends and their stored intermediate content. `probeOldEFunctor_comp₂_blockSucc` identifies the literal global induction coordinate at a double successor with evaluation at that predecessor followed by those two block inductions.

`probeOldEFunctor_comp₂_isZero` proves that an absent double predecessor has the actual zero evaluated module. The proof includes the case where the outer predecessor exists and the inner predecessor is absent: additive induction sends that inner zero module to zero.

The producer and paired concrete regular-probe consumer pass strict scoped checks with warnings as errors and both compatibility settings. The consumer tests a nonempty mixed source and both absent cases. All four owned declarations pass the standard axiom audit. Full package integration remains separate. The supported coordinate equality is the transport input for the prescribed global OLD probe equal crossing.

The source head `4da876539f5147f00b608e0f0abf9f53f5808a92` passed the
full build, global axiom audit and every non-vacuity consumer in
[#1013](https://github.com/apellis/odd-lean/pull/1013)
([CI run](https://github.com/apellis/odd-lean/actions/runs/41687376775)),
merged at `73318d56`.
