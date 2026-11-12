import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientComparison
import Mathlib.CategoryTheory.Whiskering

/-! # Naturality of weighted quotient induction
The old/truncated action comparison in SwappedVacuumCoordinates §6 must
intertwine all module maps, including both homogeneous parities.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

def inductionFunctorIsoOfEq (J K : C ⥤ D)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K) :
    induction (k := k) J ≅ induction (k := k) K := by
  subst K
  exact Iso.refl _

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

@[simp] theorem weightedRestrictionModuleIso_inv_app
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (p : ZMod 2)
    (v : OldCategory D Sc cutoff) :
    (weightedRestrictionModuleIso D Sc cutoff N M hM).inv.app p v =
      if p = 0 then LinearMap.id else 0 := rfl

@[simp] theorem quotientInductionCounitIso_hom
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (quotientInductionCounitIso D Sc cutoff N M).hom =
      (BalancedInduction.adjunctionCounit Q).app M := by
  apply Superfunctor.hom_ext
  intro p v
  rfl

end OddMath.QuiverHecke.ELVOld
