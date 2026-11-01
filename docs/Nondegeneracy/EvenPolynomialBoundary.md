# Independent S for an even moving colour

This is the parity-zero polynomial projection in
[DeformedMackeyBoundary](DeformedMackeyBoundary.md), equation (5).
The implementation is
[ELVEvenPolynomialBoundary](../../OddMath/QuiverHecke/CyclotomicAction/ELVEvenPolynomialBoundary.lean).

Canonical arbitrary-Hom long sections restrict to the existing normalized
diagonal sections: their moving tails have identical tail keys. Equality of
the two exact chronological kernels then identifies the extraction maps.
This compatibility holds at either moving parity and retains all old
coefficients.

At even moving colour, let σ be ordinary finite coefficient shift.
The iterated moving intertwiner extracts to σ^d S, where S is independently
defined by the ordered square product. The existing ordered reverse-QP
identity and actual C0P factorization give

    offDiagonalPolynomialBoundary (σ^d S)
      = C0 [x^d · appendQPProduct · endpointELV].

All source conventions are retained. No even-support restriction is imposed
on S: parity of the moving colour is zero, so its shift acts trivially on
every old coefficient at every degree. The concrete consumer uses connected
mixed-parity data and both diagonal compatibility maps.

The support bounds and top coefficients are developed in
[EvenBoundaryLeading](EvenBoundaryLeading.md), using the recurrence in
[EvenBoundaryRecurrence](EvenBoundaryRecurrence.md) and the independent-S
product bounds in [EvenSRightProduct](EvenSRightProduct.md).

Verification status and remaining dependencies are maintained in
[STATUS.md](STATUS.md) and [HANDOFF.md](HANDOFF.md).
