# The signed probe polynomial on the vacuum block

This supplies the probe annihilator required by `SwappedVacuumBubbles.md`, equation (5), and `SwappedVacuumNonpositiveBubbles.md`, equations (8)–(9). The source content is empty throughout. The original defining relation is a first-dot relation, so no same-exponent claim for arbitrary last dots or higher contents is made.

`probeOrdinaryVacuumDot_polynomial` proves the raw relation

    (a^(probeDotExponent i) - 1)^(m i) = 0

for the literal ordinary append dot at every empty-content source object. Its proof uses the injective map from the actual ordinary quotient endomorphisms to the actual cyclotomic word corner. On this one-letter block, the appended dot is exactly the first dot, and the defining generator supplies the relation.

The sign step is an identity on the original balanced quotient. For an odd homogeneous source family a, let x be its prescribed `BalancedInduction.transformLinear`. `transformLinear_square_add_one` identifies x²+1 with the negative transform of a²−1. The proof retains the parity twist on the full tensor kernel. Existing signed iteration then yields `transformLinear_odd_probe_polynomial`:

    (a_v² - 1)^m = 0 for every v  =>  (x² + 1)^m = 0.

`probeOrdinaryVacuumInductionDot_odd` applies this to every actual source supermodule and every target in the literal ordinary one-letter probe category. `probeOrdinaryVacuumModuleDot_odd` proves the same identity for the entire induced supermodule endomorphism, using total evaluation and independence of its two parity components.

The inherited pre dot acts by literal precomposition on supernatural module Homs. `probeOrdinaryVacuumModuleHom_capPolynomial` provides exactly the finite-polynomial hypothesis consumed by `SwappedVacuum.principal_inverse_cap` and `SwappedVacuum.negative_cap_annihilates_mate`:

    capPolynomial c (2*m) x_pre = 0,
    c_n = coefficient_n ((T²+1)^m).

Here the Hom block is out of the actual induced ordinary probe vacuum and into an arbitrary supermodule over the same one-letter category. Precomposition is not given an additional parity twist. The analogous pointwise SVec Hom statement and its finite-polynomial form are also proved.

`additiveFunctor_odd_probe_polynomial` transports the relation along the specified additive comparison functor. In particular, `probeOrdinaryVacuumParityDot_odd` uses the chosen SVec parity-shift functor, including its prescribed sign on odd maps. It does not replace that functor by an unsigned identification.

The paired consumer uses the actual regular height-zero probe module, its existing ordinary descent, and probe exponents one and two. It checks the actual component, entire-module, supernatural-Hom, finite-polynomial and parity-shift statements. A separate occupied signed plane checks that the plus-one polynomial and its Hom-precomposition action have nonzero dot action. This plane is a sign test, not an identification of the probe coend with that plane. All declarations owned by both producers are audited.

Attachment to the final swapped factor still needs its specified old/scalar and chosen content charts, and the concrete mate slide and cup/cap normalization. This result supplies the polynomial input; it does not assume or construct those remaining maps. The ordinary probe vacuum's nonzero induction object is not asserted by this consumer.
