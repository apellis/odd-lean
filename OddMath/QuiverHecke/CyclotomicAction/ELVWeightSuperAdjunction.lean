/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules
import OddMath.SKM.RouquierData

/-! # The actual full-ELV induction/restriction superadjunction

The existing ordinary weight adjunction has even unit and counit. They are
lifted to supernatural transformations and packaged in the actual PiSCat
action target. No local-inverse or factor-family assumption is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The weight-space unit as an even supernatural transformation. -/
def elvActionUnit : 𝟙 _ ⟶ elvE D Sc cutoff bound i Λ h ≫ elvF D Sc cutoff bound i Λ h :=
  SuperNatTrans.ofNatTrans (elvWeightUnit D Sc cutoff bound i Λ h)
    (elvWeightUnit_mem D Sc cutoff bound i Λ h)

/-- The weight-space counit as an even supernatural transformation. -/
def elvActionCounit : elvF D Sc cutoff bound i Λ h ≫ elvE D Sc cutoff bound i Λ h ⟶ 𝟙 _ :=
  SuperNatTrans.ofNatTrans (elvWeightCounit D Sc cutoff bound i Λ h)
    (elvWeightCounit_mem D Sc cutoff bound i Λ h)

/-- **The even adjunction `E_i ⊣ F_i` on weight spaces** in the Rouquier interface. -/
def elvActionAdjunction :
    SKM.SuperAdjunction (k := k) (elvE D Sc cutoff bound i Λ h) (elvF D Sc cutoff bound i Λ h) where
  unit := elvActionUnit D Sc cutoff bound i Λ h
  counit := elvActionCounit D Sc cutoff bound i Λ h
  unit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  counit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  left_triangle := by
    simp only [SCat.leftUnitor_inv, SCat.associator_hom, SCat.rightUnitor_hom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    apply Superfunctor.hom_ext_parity
    · intro M
      change _ = 𝟙 ((elvEFunctor D Sc cutoff bound i Λ h).obj M)
      simp [elvActionUnit, elvActionCounit, SuperNatTrans.ofNatTrans,
        elvE, Superfunctor.map,
        Superfunctor.obj]
      exact (elvWeightAdjunction D Sc cutoff bound i Λ h).left_triangle_components M
    · intro M
      simp [elvActionUnit, elvActionCounit, SuperNatTrans.ofNatTrans]
  right_triangle := by
    simp only [SCat.rightUnitor_inv, SCat.associator_inv, SCat.leftUnitor_hom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    apply Superfunctor.hom_ext_parity
    · intro N
      change _ = 𝟙 ((elvF D Sc cutoff bound i Λ h).toFunctor.obj N)
      simp [elvActionUnit, elvActionCounit, SuperNatTrans.ofNatTrans,
        elvF, Superfunctor.map,
        Superfunctor.obj]
      exact (elvWeightAdjunction D Sc cutoff bound i Λ h).right_triangle_components N
    · intro N
      simp [elvActionUnit, elvActionCounit, SuperNatTrans.ofNatTrans]

end OddMath.QuiverHecke.ELVOld
