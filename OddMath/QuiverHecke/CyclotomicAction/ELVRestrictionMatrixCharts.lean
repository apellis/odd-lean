import OddMath.Algebra.FiniteSupermoduleFamily
import OddMath.QuiverHecke.CyclotomicAction.ELVParityRestrictionComparison

/-! # Restriction charts for finite parity families

Brundan–Ellis (1.13)–(1.14) compares the prescribed finite module matrices
through even source, target and value charts. Restriction commutes with
the chosen finite products, while the existing parity coordinates specify
each shifted comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (Q : C ⥤ D) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]

/-- The pointwise product carries the same restricted action in each coordinate. -/
def restrictionProductIso {ι : Type} (F : ι → Superfunctor k D (SVec k)) :
    (restriction Q).obj (OddMath.FiniteSupermodule.product F) ≅
      OddMath.FiniteSupermodule.product (fun a => (restriction Q).obj (F a)) :=
  Iso.refl _

/-- The chosen pointwise comparison of all module coordinates. -/
def restrictionFamilyIso {ι : Type}
    (F : ι → Superfunctor k C (SVec k)) (G : ι → Superfunctor k D (SVec k))
    (e : ∀ a, F a ≅ (restriction Q).obj (G a)) :
    OddMath.FiniteSupermodule.product F ≅ (restriction Q).obj (OddMath.FiniteSupermodule.product G) :=
  OddMath.FiniteSupermodule.productIso e

theorem restrictionFamilyIso_hom_mem {ι : Type}
    (F : ι → Superfunctor k C (SVec k)) (G : ι → Superfunctor k D (SVec k))
    (e : ∀ a, F a ≅ (restriction Q).obj (G a))
    (he : ∀ a, (e a).hom ∈ parity (R := k) _ _ 0) :
    (restrictionFamilyIso Q F G e).hom ∈ parity (R := k) _ _ 0 :=
  OddMath.FiniteSupermodule.productIso_hom_mem e he

/-- Every coordinate is the specified module comparison, on arbitrary input vectors. -/
theorem restrictionFamilyIso_total_apply {ι : Type}
    (F : ι → Superfunctor k C (SVec k)) (G : ι → Superfunctor k D (SVec k))
    (e : ∀ a, F a ≅ (restriction Q).obj (G a)) (w : C)
    (x : (OddMath.FiniteSupermodule.product F).obj w) (a : ι) :
    (restrictionFamilyIso Q F G e).hom.total w x a = (e a).hom.total w (x a) := rfl

variable (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (e : M ≅ (restriction Q).obj N)
local instance restrictionMatrixSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
local instance restrictionMatrixTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) :=
  supermodulePiSupercategory

/-- Shift the selected chart using the prescribed restriction/parity comparison. -/
def shiftedRestrictionChart (q : ZMod 2) :
    (SKM.homParityShift (k := k) q).obj M ≅
      (restriction Q).obj ((SKM.homParityShift (k := k) q).obj N) :=
  (parityRestrictionIso Q N M e.symm q).symm

theorem shiftedRestrictionChart_hom_mem (q : ZMod 2)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (shiftedRestrictionChart Q M N e q).hom ∈ parity (R := k) _ _ 0 :=
  parityRestrictionIso_inv_mem Q N M e.symm q (inv_mem _ he)

theorem shiftedRestrictionChart_source_coordinate (q : ZMod 2)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (shiftedRestrictionChart Q M N e q).hom ≫
        (restriction Q).map ((SKM.homParityShiftDatum (k := k) q).iso N).hom =
      ((SKM.homParityShiftDatum (k := k) q).iso M).hom ≫ e.hom := by
  have h := parityRestrictionIso_hom_coordinate Q N M e.symm q (inv_mem _ he)
  simp only [Iso.symm_hom] at h
  apply (cancel_mono e.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← h]
  simp only [shiftedRestrictionChart, Iso.symm_hom, Iso.inv_hom_id_assoc]

end OddMath.QuiverHecke.ELVOld.BalancedInduction
