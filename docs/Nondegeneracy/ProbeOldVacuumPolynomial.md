# The signed probe polynomial on the old vacuum coend

This attaches the signed probe annihilator of `ProbeVacuumPolynomial.md` to the unchanged old coend used in `SwappedVacuumBubbles.md`, equation (5). The source content is empty. No same-exponent assertion about a last dot at arbitrary higher content is made.

Let N be an old empty-content supermodule satisfying the existing `ProbeEvaluatesCoefficients` property. The original scalar-evaluated probe modules have this property by `probeOldModule_evaluatesCoefficients`; the paired consumer discharges it on their regular height-zero module.

The comparison is the specified `probeAppendOrdinaryModuleIso`, evaluated on the target word. Its forward linear map is precisely `probeAppendComparisonLinear`. `probeAppendOrdinaryModuleIso_hom_dot` intertwines the given signed `probeOldContentInductionDot` with the prescribed signed ordinary induction dot. The comparison's inverse proves injectivity on the original coend. Intertwining powers of x²+1 then transports the proved ordinary annihilator back to the old source:

    (probeOldContentInductionDot² + 1)^(m_i) = 0.

This is `probeOldVacuumInductionDot_odd`, with the original coefficient action, vector carrier and signed dot. It does not define a replacement old action or require flatness of scalar specialization.

`probeOldVacuumModuleDot_odd` proves the relation before component evaluation, as an identity of endomorphisms of the entire old induced supermodule. The proof uses total evaluation, its compatibility with endomorphism powers, and independence of the two parity components.

`probeOldVacuumModuleHom_capPolynomial` gives the finite polynomial input to the inverse-cap recovery library on the original supernatural Hom block:

    capPolynomial c (2*m_i) x_pre = 0,
    c_n = coefficient_n ((T²+1)^(m_i)),
    x_pre(f) = x ; f.

Here x is the prescribed old induced-module dot and the target supermodule is arbitrary. Precomposition acts on the full Hom space, including its odd and inhomogeneous transformations. It is ordinary categorical precomposition; no additional total-Hom twist is inserted. The chosen parity and content charts of the final swapped action still have to identify its dot with this operator or its specified additive image.

The consumer checks the original old coend, the whole old module and the finite supernatural-Hom annihilator on the canonical regular height-zero probe at exponents one and two. The scalar-evaluation property is proved, and every declaration owned by the producer is audited. As in the preceding batch, it does not assert that the actual induced probe object is nonzero. Final swapped mate slides, inverse-cap identification and bubble normalization remain separate attachments.
