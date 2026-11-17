import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop.WeightedInductionNaturality

/-!
# Content modules

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Tensor formulas for weighted append comparison
SwappedVacuumCoordinates §6 requires compatibility with the specified
generators, beyond pointwise or input-module naturality.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory

namespace OddMath.QuiverHecke.ELV
universe u
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

theorem moduleIsoOfEvenNatIso_inv_total (F G : Superfunctor k C (SVec k))
    (e : F.toFunctor ≅ G.toFunctor)
    (hh : ∀ w, e.hom.app w ∈ parity (R := k) _ _ 0)
    (hi : ∀ w, e.inv.app w ∈ parity (R := k) _ _ 0) (w : C) :
    (moduleIsoOfEvenNatIso F G e hh hi).inv.total w = e.inv.app w := by
  change e.inv.app w + (0 : G.obj w ⟶ F.obj w) = e.inv.app w
  exact add_zero _

end OddMath.QuiverHecke.ELV

namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

omit [Supercategory k D] in
private theorem tensor_identity_add_zero (J : C ⥤ D)
    (M : Superfunctor k C (SVec k)) (v : C) (w : D)
    (g h : J.obj v ⟶ w) (b : M.obj v) :
    tensor J M.toFunctor v g ((LinearMap.id : M.obj v →ₗ[k] M.obj v) b) +
      tensor J M.toFunctor v h ((0 : M.obj v →ₗ[k] M.obj v) b) =
        tensor J M.toFunctor v g b := by
  rw [LinearMap.id_apply, LinearMap.zero_apply, tensor_zero_right, add_zero]

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

@[simp] theorem weightedRestrictionModuleIso_hom_app
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (p : ZMod 2)
    (v : OldCategory D Sc cutoff) :
    (weightedRestrictionModuleIso D Sc cutoff N M hM).hom.app p v =
      if p = 0 then LinearMap.id else 0 := rfl

theorem quotientInductionCounitIso_inv_total
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (w : TruncatedCategory D Sc cutoff N) :
    (quotientInductionCounitIso D Sc cutoff N M).inv.total w =
      BalancedInduction.unit Q (Q ⋙ M.toFunctor) ⟨w.word⟩ :=
  moduleIsoOfEvenNatIso_inv_total _ _ _ _ _ w

/-- The inverse quotient/descent comparison is the canonical unit tensor
on the same old vector space. -/
theorem quotientInducedWeightedModuleIso_inv_tensor
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M)
    (w : TruncatedCategory D Sc cutoff N) (b : M.obj ⟨w.word⟩) :
    (quotientInducedWeightedModuleIso D Sc cutoff N M hM).inv.total w b =
      BalancedInduction.tensor Q M.toFunctor
        (⟨w.word⟩ : OldCategory D Sc cutoff) (𝟙 w) b := by
  let S := weightedModule D Sc cutoff N M hM
  let u := weightedRestrictionModuleIso D Sc cutoff N M hM
  let c := quotientInductionCounitIso D Sc cutoff N S
  let IQ := BalancedInduction.induction (k := k) Q
  have hc : c.inv.total w b =
      BalancedInduction.tensor Q (weightedRestriction D Sc cutoff N S).toFunctor
        (⟨w.word⟩ : OldCategory D Sc cutoff) (𝟙 w) b := by
    rw [quotientInductionCounitIso_inv_total]
    rfl
  have ht : (quotientInducedWeightedModuleIso D Sc cutoff N M hM).inv.total w =
      (IQ.map u.hom).total w ∘ₗ c.inv.total w := by
    change (c.inv ≫ IQ.map u.hom).total w = _
    exact Superfunctor.comp_total _ _ w
  have hv : (quotientInducedWeightedModuleIso D Sc cutoff N M hM).inv.total w b =
      (IQ.map u.hom).total w (c.inv.total w b) :=
    congrArg (fun f : S.obj w →ₗ[k] BalancedInduction.Obj Q M.toFunctor w => f b) ht
  refine hv.trans ?_
  refine (congrArg ((IQ.map u.hom).total w) hc).trans ?_
  change (BalancedInduction.moduleMap Q u.hom).total w
    (BalancedInduction.tensor Q (weightedRestriction D Sc cutoff N S).toFunctor
      (⟨w.word⟩ : OldCategory D Sc cutoff) (𝟙 w) b) = _
  rw [BalancedInduction.moduleMap_total_tensor]
  simp only [u, weightedRestrictionModuleIso_hom_app, ↓reduceIte, one_ne_zero]
  exact BalancedInduction.tensor_identity_add_zero Q M
    (⟨w.word⟩ : OldCategory D Sc cutoff) w (𝟙 w) (twist k 1 (𝟙 w)) b

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Parity of weighted append comparison
The generator transport in SwappedVacuumCoordinates §6 uses the evenness of
the specified five-isomorphism comparison, before evaluating its unit tensors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV

namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end
