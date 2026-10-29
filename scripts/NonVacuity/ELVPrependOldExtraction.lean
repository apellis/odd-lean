import OddMath.QuiverHecke.CyclotomicAction.ELVPrependOldExtraction
import NonVacuity.ELVPrependCoordinates

noncomputable section
namespace ELVPrependOldExtractionConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld ELVPrependConsumer
open scoped TensorProduct

/-- An inhomogeneous exterior coefficient on the old identity diagram. -/
def oldCoefficient : hom datum scalars (fun _ => 3) [()] movingIndex.oldTarget :=
  ((1 : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) datum (fun _ => 3)) + delta)
    ⊗ₜ[ℚ] movingIndex.old.nf

example := prependAffineEquiv_insert_tail datum scalars (fun _ => 3)
  movingIndex oldCoefficient

/-- Both the odd tail normalization and the total-parity twist occur. -/
example := prependExtractOld_insert_tail datum scalars (fun _ => 3)
  1 movingIndex oldCoefficient

/-- Composition is not restricted to homogeneous or basis old morphisms. -/
example (r : hom datum scalars (fun _ => 3) [()] [()])
    (b : hom datum scalars (fun _ => 3) [()] movingIndex.oldTarget) :
    prependExtractOld datum scalars (fun _ => 3) 1 movingIndex
      (insert datum scalars (fun _ => 3) () [()] [()] r ≫
        insert datum scalars (fun _ => 3) () [()] movingIndex.oldTarget b ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) datum (fun _ => 3)) ⊗ₜ[ℚ]
          prependTail datum scalars movingIndex :
            hom datum scalars (fun _ => 3) (() :: movingIndex.oldTarget) [(), ()])) =
      twist ℚ 1 (r ≫ b) :=
  prependExtractOld_insert_comp_tail datum scalars (fun _ => 3) 1 movingIndex r b

example := prependExtractOldQuotient_insert_tail datum scalars (fun _ => 3)
  1 movingIndex oldCoefficient
example := prependExtractOldQuotient_insert_tail_eq_zero_iff datum scalars (fun _ => 3)
  1 movingIndex oldCoefficient

#print axioms prependAffineEquiv_insert_tail
#print axioms prependExtractOld_insert_comp_tail
#print axioms prependExtractOldQuotient_insert_tail_eq_zero_iff
end ELVPrependOldExtractionConsumer
