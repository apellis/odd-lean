# Canonical upper-Hom comparison for old quotient modules

Status: full build, global axiom audit and concrete consumers passed before research integration in #806, including the canonical old append superfunctor.

ELVOldInductionRepresentable constructs the even natural module isomorphism from right-append induction of the old Hom representable to the representable of the appended word. Its forward map is [h tensor b] ↦ append(b) composed with h; its inverse inserts the old identity. The upperHomEquiv is the resulting concrete identification of Res(Ind representable_v) at t with Old(v+i,t+i). No target-isomorphism, field, flatness or action premise is supplied.

This is the canonical target comparison for DeformedMatrixComparison (4). Remaining: normalized double-append crossing and its actual adjunction mate component evaluation, dotted cups, source checks, and transport to coefficient-truncated exact-content module categories. The truncation ideal is homogeneous and may contain odd coefficient monomials, so later transport must respect its full super signs.
