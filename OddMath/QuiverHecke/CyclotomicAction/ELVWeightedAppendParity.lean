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

private theorem fiveIsoHom_mem
    {B : Type*} [Category* B] [Preadditive B] [Linear k B] [Supercategory k B]
    {F₀ F₁ F₂ F₃ F₄ F₅ : B}
    (e₁ : F₀ ≅ F₁) (e₂ : F₁ ≅ F₂) (e₃ : F₂ ≅ F₃)
    (e₄ : F₃ ≅ F₄) (e₅ : F₄ ≅ F₅)
    (h₁ : e₁.hom ∈ parity (R := k) _ _ 0)
    (h₂ : e₂.hom ∈ parity (R := k) _ _ 0)
    (h₃ : e₃.hom ∈ parity (R := k) _ _ 0)
    (h₄ : e₄.hom ∈ parity (R := k) _ _ 0)
    (h₅ : e₅.hom ∈ parity (R := k) _ _ 0) :
    (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅).hom ∈ parity (R := k) _ _ 0 := by
  simpa only [Iso.trans_hom, zero_add] using
    comp_mem h₁ (comp_mem h₂ (comp_mem h₃ (comp_mem h₄ h₅)))

end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

theorem inducedIsoOfFunctorEq_hom_mem (J K : C ⥤ D)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K)
    (M : Superfunctor k C (SVec k)) :
    (inducedIsoOfFunctorEq J K h M).hom ∈ parity (R := k) _ _ 0 := by
  subst K
  change (𝟙 (induced J M)) ∈ parity (R := k) _ _ 0
  exact id_mem _

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

theorem weightedRestrictionModuleIso_inv_mem
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    (weightedRestrictionModuleIso D Sc cutoff N M hM).inv ∈ parity (R := k) _ _ 0 :=
  Supercategory.inv_mem (weightedRestrictionModuleIso D Sc cutoff N M hM)
    (weightedRestrictionModuleIso_hom_mem D Sc cutoff N M hM)

theorem quotientInductionCounitIso_hom_mem
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (quotientInductionCounitIso D Sc cutoff N M).hom ∈ parity (R := k) _ _ 0 := by
  rw [quotientInductionCounitIso_hom]
  exact BalancedInduction.adjunctionCounit_mem Q M

theorem quotientInducedWeightedModuleIso_hom_mem
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    (quotientInducedWeightedModuleIso D Sc cutoff N M hM).hom ∈ parity (R := k) _ _ 0 := by
  let e := weightedRestrictionModuleIso D Sc cutoff N M hM
  let c := quotientInductionCounitIso D Sc cutoff N (weightedModule D Sc cutoff N M hM)
  have he : e.inv ∈ parity (R := k) _ _ 0 :=
    weightedRestrictionModuleIso_inv_mem D Sc cutoff N M hM
  have hc : c.hom ∈ parity (R := k) _ _ 0 :=
    quotientInductionCounitIso_hom_mem D Sc cutoff N _
  have hm := IsSuperfunctor.map_mem (F := BalancedInduction.induction Q) he
  change (BalancedInduction.induction Q).map e.inv ≫ c.hom ∈ parity (R := k) _ _ 0
  simpa only [zero_add] using comp_mem hm hc

theorem quotientInducedWeightedModuleIso_inv_mem
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    (quotientInducedWeightedModuleIso D Sc cutoff N M hM).inv ∈ parity (R := k) _ _ 0 :=
  Supercategory.inv_mem (quotientInducedWeightedModuleIso D Sc cutoff N M hM)
    (quotientInducedWeightedModuleIso_hom_mem D Sc cutoff N M hM)

/-- Every leg of the chosen old/truncated append comparison is even. -/
theorem appendWeightedModuleIso_hom_mem (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (appendWeightedModuleIso D Sc cutoff N i M).hom ∈ parity (R := k) _ _ 0 := by
  unfold appendWeightedModuleIso
  apply fiveIsoHom_mem
  · exact quotientInducedWeightedModuleIso_inv_mem D Sc cutoff N _ _
  · exact BalancedInduction.inductionComp_hom_mem _ _ _
  · exact BalancedInduction.inducedIsoOfFunctorEq_hom_mem _ _ _ _
  · exact BalancedInduction.inductionComp_inv_mem _ _ _
  · exact IsSuperfunctor.map_mem (F := BalancedInduction.induction _)
      (quotientInductionCounitIso_hom_mem D Sc cutoff N M)

theorem appendWeightedModuleIso_inv_mem (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (appendWeightedModuleIso D Sc cutoff N i M).inv ∈ parity (R := k) _ _ 0 :=
  Supercategory.inv_mem (appendWeightedModuleIso D Sc cutoff N i M)
    (appendWeightedModuleIso_hom_mem D Sc cutoff N i M)

end OddMath.QuiverHecke.ELVOld
