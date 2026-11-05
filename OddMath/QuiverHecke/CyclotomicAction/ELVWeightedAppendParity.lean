import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientTensors

/-! # Parity of weighted append comparison
The generator transport in SwappedVacuumCoordinates §6 uses the evenness of
the specified five-isomorphism comparison, before evaluating its unit tensors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

theorem moduleIsoOfEvenNatIso_hom_mem (F G : Superfunctor k C (SVec k))
    (e : F.toFunctor ≅ G.toFunctor)
    (hh : ∀ w, e.hom.app w ∈ parity (R := k) _ _ 0)
    (hi : ∀ w, e.inv.app w ∈ parity (R := k) _ _ 0) :
    (moduleIsoOfEvenNatIso F G e hh hi).hom ∈ parity (R := k) F G 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext w
  change (if q = 0 then e.hom.app w else 0) = 0
  exact ite_eq_right hq

theorem moduleIsoOfEvenNatIso_inv_mem (F G : Superfunctor k C (SVec k))
    (e : F.toFunctor ≅ G.toFunctor)
    (hh : ∀ w, e.hom.app w ∈ parity (R := k) _ _ 0)
    (hi : ∀ w, e.inv.app w ∈ parity (R := k) _ _ 0) :
    (moduleIsoOfEvenNatIso F G e hh hi).inv ∈ parity (R := k) G F 0 :=
  Supercategory.inv_mem (moduleIsoOfEvenNatIso F G e hh hi)
    (moduleIsoOfEvenNatIso_hom_mem F G e hh hi)

end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

theorem weightedRestrictionModuleIso_hom_mem
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    (weightedRestrictionModuleIso D Sc cutoff N M hM).hom ∈ parity (R := k) _ _ 0 := by
  unfold weightedRestrictionModuleIso
  exact moduleIsoOfEvenNatIso_hom_mem _ _ _ _ _

theorem quotientInductionCounitIso_hom_mem
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (quotientInductionCounitIso D Sc cutoff N M).hom ∈ parity (R := k) _ _ 0 := by
  rw [quotientInductionCounitIso_hom]
  exact BalancedInduction.adjunctionCounit_mem Q M

end OddMath.QuiverHecke.ELVOld
