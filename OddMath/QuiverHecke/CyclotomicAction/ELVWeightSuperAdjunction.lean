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

private def ordinaryEvenSuperAdjunction
    {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (F : B ⟶ A)
    (adj : E.toFunctor ⊣ F.toFunctor)
    (hη : ∀ M, adj.unit.app M ∈ parity (R := k) _ _ 0)
    (hε : ∀ N, adj.counit.app N ∈ parity (R := k) _ _ 0) :
    SKM.SuperAdjunction (k := k) E F where
  unit := SuperNatTrans.ofNatTrans adj.unit hη
  counit := SuperNatTrans.ofNatTrans adj.counit hε
  unit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  counit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  left_triangle := by
    apply Superfunctor.hom_ext_parity
    · intro M
      simp [SuperNatTrans.ofNatTrans, Superfunctor.map, Superfunctor.obj]
    · intro M
      simp [SuperNatTrans.ofNatTrans]
  right_triangle := by
    apply Superfunctor.hom_ext_parity
    · intro N
      simp [SuperNatTrans.ofNatTrans, Superfunctor.map, Superfunctor.obj]
    · intro N
      simp [SuperNatTrans.ofNatTrans]

/-- The actual even induction/restriction adjunction in the PiSCat target. -/
def elvActionAdjunction :
    SKM.SuperAdjunction (k := k) (elvE D Sc cutoff bound i Λ h)
      (elvF D Sc cutoff bound i Λ h) :=
  ordinaryEvenSuperAdjunction (elvE D Sc cutoff bound i Λ h)
    (elvF D Sc cutoff bound i Λ h) (elvWeightAdjunction D Sc cutoff bound i Λ h)
    (elvWeightUnit_mem D Sc cutoff bound i Λ h)
    (elvWeightCounit_mem D Sc cutoff bound i Λ h)

end OddMath.QuiverHecke.ELVOld
