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

theorem weightedRestrictionModuleIso_inv_naturality
    (M L : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M)
    (hL : KillsWeightedCoefficients D Sc cutoff N L) (f : M ⟶ L) :
    f ≫ (weightedRestrictionModuleIso D Sc cutoff N L hL).inv =
      (weightedRestrictionModuleIso D Sc cutoff N M hM).inv ≫
        (BalancedInduction.restriction Q).map
          (weightedModuleHom D Sc cutoff N M L hM hL f) := by
  apply Superfunctor.hom_ext
  intro p v
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change (LinearMap.id : L.obj v →ₗ[k] L.obj v) ∘ₗ f.app 0 v +
      (0 : L.obj v →ₗ[k] L.obj v) ∘ₗ f.app 1 v =
      f.app 0 v ∘ₗ (LinearMap.id : M.obj v →ₗ[k] M.obj v) +
      f.app 1 v ∘ₗ (0 : M.obj v →ₗ[k] M.obj v)
    simp only [LinearMap.id_comp, LinearMap.zero_comp, LinearMap.comp_id,
      LinearMap.comp_zero, add_zero]
  · change (0 : L.obj v →ₗ[k] L.obj v) ∘ₗ f.app 0 v +
      (LinearMap.id : L.obj v →ₗ[k] L.obj v) ∘ₗ f.app 1 v =
      f.app 1 v ∘ₗ (LinearMap.id : M.obj v →ₗ[k] M.obj v) +
      f.app 0 v ∘ₗ (0 : M.obj v →ₗ[k] M.obj v)
    simp only [LinearMap.id_comp, LinearMap.zero_comp, LinearMap.comp_id,
      LinearMap.comp_zero, add_zero, zero_add]

@[simp] theorem quotientInductionCounitIso_hom
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (quotientInductionCounitIso D Sc cutoff N M).hom =
      (BalancedInduction.adjunctionCounit Q).app M := by
  apply Superfunctor.hom_ext
  intro p v
  rfl

/-- The canonical quotient-induction/descent comparison is natural in all
supermodule maps; no evenness assumption is imposed on the map. -/
theorem quotientInducedWeightedModuleIso_naturality
    (M L : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M)
    (hL : KillsWeightedCoefficients D Sc cutoff N L) (f : M ⟶ L) :
    (BalancedInduction.induction Q).map f ≫
        (quotientInducedWeightedModuleIso D Sc cutoff N L hL).hom =
      (quotientInducedWeightedModuleIso D Sc cutoff N M hM).hom ≫
        weightedModuleHom D Sc cutoff N M L hM hL f := by
  let IQ := BalancedInduction.induction (k := k) Q
  let RQ := BalancedInduction.restriction (k := k) Q
  let wf := weightedModuleHom D Sc cutoff N M L hM hL f
  let uM := weightedRestrictionModuleIso D Sc cutoff N M hM
  let uL := weightedRestrictionModuleIso D Sc cutoff N L hL
  let cM := (quotientInductionCounitIso D Sc cutoff N
    (weightedModule D Sc cutoff N M hM)).hom
  let cL := (quotientInductionCounitIso D Sc cutoff N
    (weightedModule D Sc cutoff N L hL)).hom
  have hr : f ≫ uL.inv = uM.inv ≫ RQ.map wf :=
    weightedRestrictionModuleIso_inv_naturality D Sc cutoff N M L hM hL f
  have hc : (RQ ⋙ IQ).map wf ≫ cL = cM ≫ wf := by
    change (RQ ⋙ IQ).map wf ≫
      (quotientInductionCounitIso D Sc cutoff N
        (weightedModule D Sc cutoff N L hL)).hom =
      (quotientInductionCounitIso D Sc cutoff N
        (weightedModule D Sc cutoff N M hM)).hom ≫ wf
    rw [quotientInductionCounitIso_hom, quotientInductionCounitIso_hom]
    exact (BalancedInduction.adjunctionCounit Q).naturality wf
  change IQ.map f ≫ (IQ.map uL.inv ≫ cL) =
    (IQ.map uM.inv ≫ cM) ≫ wf
  calc
    IQ.map f ≫ (IQ.map uL.inv ≫ cL) = IQ.map (f ≫ uL.inv) ≫ cL := by
      rw [Functor.map_comp, Category.assoc]
    _ = IQ.map (uM.inv ≫ RQ.map wf) ≫ cL := by rw [hr]
    _ = IQ.map uM.inv ≫ ((RQ ⋙ IQ).map wf ≫ cL) := by
      rw [Functor.map_comp, Category.assoc]
      rfl
    _ = IQ.map uM.inv ≫ (cM ≫ wf) := by rw [hc]
    _ = (IQ.map uM.inv ≫ cM) ≫ wf := (Category.assoc _ _ _).symm

private theorem iso_inv_naturality {C : Type*} [Category C]
    {A B A' B' : C} (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : f ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv = e.inv ≫ f := by
  apply (cancel_mono e'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Descent of a functor whose values kill the weighted coefficient ideal.
Keeping the functor abstract makes identity and composition independent of
the concrete coend presentation. -/
def weightedFunctorDescent {C : Type*} [Category C]
    (F : C ⥤ Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hF : ∀ M, KillsWeightedCoefficients D Sc cutoff N (F.obj M)) :
    C ⥤ Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) where
  obj M := weightedModule D Sc cutoff N (F.obj M) (hF M)
  map {M L} f := weightedModuleHom D Sc cutoff N
    (F.obj M) (F.obj L) (hF M) (hF L) (F.map f)
  map_id M := by
    rw [F.map_id]
    exact weightedModuleHom_id D Sc cutoff N (F.obj M) (hF M)
  map_comp {M L P} f g := by
    rw [F.map_comp]
    exact weightedModuleHom_comp D Sc cutoff N
      (F.obj M) (F.obj L) (F.obj P) (hF M) (hF L) (hF P) (F.map f) (F.map g)

/-- Descended old append induction, including every module map. -/
def weightedAppendFunctor (i : I) :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) ⥤
      Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) :=
  weightedFunctorDescent D Sc cutoff N
    (BalancedInduction.restriction Q ⋙
      BalancedInduction.induction (CyclotomicCrossingTensor.append D Sc cutoff i))
    (fun M => induced_killsWeightedCoefficients D Sc cutoff N i
      (weightedRestriction D Sc cutoff N M) (weightedRestriction_kills D Sc cutoff N M))

def weightedAppendQuotientIso (i : I) :
    weightedAppendFunctor D Sc cutoff N i ≅
      BalancedInduction.restriction Q ⋙
        BalancedInduction.induction (CyclotomicCrossingTensor.append D Sc cutoff i) ⋙
          BalancedInduction.induction Q :=
  NatIso.ofComponents (fun M =>
    (quotientInducedWeightedModuleIso D Sc cutoff N
      (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i)
        (weightedRestriction D Sc cutoff N M))
      (induced_killsWeightedCoefficients D Sc cutoff N i
        (weightedRestriction D Sc cutoff N M) (weightedRestriction_kills D Sc cutoff N M))).symm)
    (by
      intro M L f
      apply iso_inv_naturality
      exact quotientInducedWeightedModuleIso_naturality D Sc cutoff N _ _ _ _
        ((BalancedInduction.induction (CyclotomicCrossingTensor.append D Sc cutoff i)).map
          ((BalancedInduction.restriction Q).map f)))

/-- The quotient-induction counit is a natural isomorphism in the module. -/
def quotientInductionCounitModuleIso :
    BalancedInduction.restriction Q ⋙ BalancedInduction.induction Q ≅
      𝟭 (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  NatIso.ofComponents (quotientInductionCounitIso D Sc cutoff N) (by
    intro M L f
    rw [quotientInductionCounitIso_hom, quotientInductionCounitIso_hom]
    exact (BalancedInduction.adjunctionCounit Q).naturality f)

/-- The old/truncated append comparison is natural for all supermodule maps. -/
def appendWeightedNaturalIso (i : I) :
    weightedAppendFunctor D Sc cutoff N i ≅
      BalancedInduction.induction (truncatedAppend D Sc cutoff N [i]) :=
  let J := CyclotomicCrossingTensor.append D Sc cutoff i
  let T := truncatedAppend D Sc cutoff N [i]
  let RQ := BalancedInduction.restriction (k := k) Q
  weightedAppendQuotientIso D Sc cutoff N i ≪≫
    Functor.isoWhiskerLeft RQ (BalancedInduction.inductionComp J Q) ≪≫
      Functor.isoWhiskerLeft RQ (BalancedInduction.inductionFunctorIsoOfEq (J ⋙ Q) (Q ⋙ T)
        (oldAppend_truncate D Sc cutoff N i)) ≪≫
      (Functor.isoWhiskerLeft RQ (BalancedInduction.inductionComp Q T)).symm ≪≫
      Functor.isoWhiskerRight (quotientInductionCounitModuleIso D Sc cutoff N)
        (BalancedInduction.induction T)

end OddMath.QuiverHecke.ELVOld
