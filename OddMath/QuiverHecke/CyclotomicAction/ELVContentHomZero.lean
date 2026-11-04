import OddMath.QuiverHecke.CyclotomicAction.ELVCategoryCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules

/-! # Zero objects in the fixed-output content Hom category

The zero padding in `SwappedHomInversion.md` §2 uses the actual zero
module at a fixed output content. Its constant superfunctor is a zero
object while retaining the entire probe input category.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction
universe u
local instance contentZeroHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The constant actual zero module, regarded as a whole-input superfunctor. -/
def contentHomZero (β : Multiset I) (A : PiSCat.{u,u,u+1} k) :
    A ⟶ contentModuleTarget D Sc cutoff bound β :=
  ⟨elvZeroFunctor D Sc cutoff bound (C := A) β⟩

/-- Its identity vanishes as a supernatural transformation, before input evaluation. -/
theorem contentHomZero_isZero (β : Multiset I) (A : PiSCat.{u,u,u+1} k) :
    Limits.IsZero (contentHomZero D Sc cutoff bound β A) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext
  intro p M
  exact (elvZeroModule_isZero D Sc cutoff bound β).eq_of_src _ _

/-- The padded fixed-output Hom category has its zero object from the source modules. -/
instance contentHom_hasZeroObject (β : Multiset I) (A : PiSCat.{u,u,u+1} k) :
    Limits.HasZeroObject (A ⟶ contentModuleTarget D Sc cutoff bound β) :=
  ⟨⟨contentHomZero D Sc cutoff bound β A, contentHomZero_isZero D Sc cutoff bound β A⟩⟩

end OddMath.QuiverHecke.ELVOld
