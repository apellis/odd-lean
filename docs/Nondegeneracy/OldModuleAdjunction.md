# Old module adjunction and ordered crossing mate

Status: producer and paired asymmetric consumer passed strict local Lean checks, including the all-owned-declaration axiom audit. Full CI pending. Target: DeformedMatrixComparison, same-colour categorical matrix-entry comparison.

ELVOldModuleAdjunction builds the canonical old-module category, the existing balanced-induction/restriction even adjunction and its signed ordered Rouquier mate. One underlying SCat record is shared literally by the Π bundle; its induction and restriction are the same constructed functors in both views. The component formula is the actual balanced unit, restriction of the signed crossing, then induced counit. No adjunction or target-isomorphism premise is supplied.

Uses the existing public ordinaryEvenSuperAdjunction constructor and the generic scat_rouquierMate_app theorem. Exact tensor evaluation under the checked old induction-representable/co-Yoneda equivalence, the positive unit/dot columns, and homogeneous coefficient-truncation/exact-content/global transport are separate consumers. No complete action or categorical matrix inverse is claimed by this bundle module.
