# Parity-preserving ELV scalar Hom specialization

The scalar evaluation on the exact untruncated ELV coefficient algebra is already integrated. `ELVScalarParity.lean` proves that every odd homogeneous coefficient evaluates to zero, using a representative argument outside the central coefficient-category module. `ELVScalarSpecializationFunctor.lean` uses the existing box-product map and unitor to construct the actual signed affine Hom specialization; it is surjective on affine Homs.

These producers, the corrected concrete parity consumer and global axiom audit passed full CI before research integration in #762. The literal polynomial comparisons are verified in #765, and the prescribed probe's original cyclotomic ideal descent in #814. The content/module-action specialization and its categorical inverse comparison remain separate obligations.
