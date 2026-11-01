# Prescribed matrices on arbitrary old supermodules

The all-module step of [DeformedMatrixComparison](DeformedMatrixComparison.md), section 4, transfers the concrete coefficient-kernel inverse through the explicit many-object balanced tensor. No general categorical colimit or flatness theorem is assumed.

ELVModuleMatrixInverse proposes moduleUnitMatrixIso and moduleCapMatrixIso for every old supermodule M and every moving colour. Their only directional conditions are the corresponding sign of contentCrossingHeight at the target; the finite counts are contentUnitCount and contentCapCount of that same content. There is no representability assumption on M and no arbitrary coefficient-bijection premise in the public statements.

The linear equivalences are built by tensoring the actual natural coefficient kernel isomorphisms, then transporting through the checked source and target coordinates. Whole forward-matrix evaluation identifies their hom maps with the literal unitMatrixComponent and capMatrixComponent. Those actual matrices already have independent evenness proofs; inverse evenness follows from the isomorphism identity.

The producer and mixed-colour consumer are staged pending the concrete global coefficient-kernel bijection and whole forward-matrix identities. The consumer keeps M arbitrary over fixed rational mixed-parity data, proves its height signs, and includes the height-zero empty window. This is pointwise matrix inversion; global content/category assembly remains separate.

The coefficient conjugation is proposed through `kernelMateRowLinear`, whose domain and codomain are the same bundled kernel objects as the prescribed coefficient. The map equality `actualMateKernelLinear_eq_row` passes the isolated strict source check. Its conversion to the existing pointwise `actualMateKernelLinear_row`, including explicit normalization of hidden instance arguments, still exceeds the existing normalization budget, so that theorem keeps its original statement and remains unverified. The downstream `ELVKernelMatrixBijective` and `ELVModuleMatrixInverse` consumers are blocked by that bridge; none of the proposed all-module inverse statements is established.
