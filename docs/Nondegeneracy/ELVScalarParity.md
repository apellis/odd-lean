# Parity-preserving ELV scalar Hom specialization

The scalar evaluation on the exact untruncated ELV coefficient algebra is already integrated. `ELVScalarParity.lean` proves that every odd homogeneous coefficient evaluates to zero, using a representative argument outside the central coefficient-category module. `ELVScalarSpecializationFunctor.lean` uses the existing box-product map and unitor to construct the actual signed affine Hom specialization; it is surjective on affine Homs.

These producers and the global axiom audit passed CI at d887fc965bff912fffe401ed7b7faddfd45c44bd. Its concrete parity consumer required only an explicit cutoff annotation, now supplied. Fresh full CI must verify the corrected consumer before integration. Cyclotomic relation descent and full action specialization are separate obligations.
