/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDot
import OddMath.QuiverHecke.SwappedAssembly.ProductDenominatorUnits

/-! # Whole dot units on every original-weight OLD probe category

SwappedActionAssembly F2: the chosen signed dot is a unit of the entire
weight-induction endomorphism ring. The actual scalar-quotient inverse
works at every predecessor; absent predecessors have the zero module.
The original weight fibre may be infinite, with no uniform exponent.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u v w t z

private def homogeneousTotalUnitIso
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (F : Superfunctor k C A) {p : ZMod 2} (f : End F) (hf : f ∈ parity (R := k) _ _ p)
    (hu : ∀ M, IsUnit (show End (F.obj M) from f.total M)) : F ≅ F :=
  OddMath.HomogeneousSuperfunctorIso.ofHom f hf
    (fun M => by
      haveI : IsIso (f.total M) := (isUnit_iff_isIso _).mp (hu M)
      exact asIso (f.total M)) (fun _ => rfl)

private theorem homogeneousTotalUnitIso_hom
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (F : Superfunctor k C A) {p : ZMod 2} (f : End F) (hf : f ∈ parity (R := k) _ _ p)
    (hu : ∀ M, IsUnit (show End (F.obj M) from f.total M)) :
    (homogeneousTotalUnitIso F f hf hu).hom = f :=
  OddMath.HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

private theorem conjugate_total
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (F : Superfunctor k C A) (f : End F) (M : C) {V : A} (hV : V = F.obj M) :
    eqToHom hV ≫ f.total M ≫ eqToHom hV.symm =
      (eqToHom hV ≫ f.app 0 M ≫ eqToHom hV.symm) +
        (eqToHom hV ≫ f.app 1 M ≫ eqToHom hV.symm) := by
  rw [SuperNatTrans.total, Preadditive.add_comp, Preadditive.comp_add]

private theorem conjugate_unit {C : Type*} [Category C] {A B : C}
    (h : A = B) (f : End B) (hf : IsUnit f) :
    IsUnit (End.of (eqToHom h ≫ f ≫ eqToHom h.symm)) := by
  cases h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hf

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- Each prescribed block dot has its constructed whole-functor inverse. -/
theorem probeOldBlockDot_isUnit (β : WeightBlocks D Λ x) :
    IsUnit (End.of (probeOldBlockDot D Sc m i Λ h β)) :=
  probeAppendToInductionDot_isUnit D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _

omit [Fintype I] in
/-- The total dot retains the selected predecessor and exact native block map. -/
theorem probeOldActionDot_total_blockSucc (M : ProbeOldWeightProduct D Sc m Λ x)
    (β : WeightBlocks D Λ x) :
    (probeOldActionDot D Sc m i Λ h).total M (blockSucc D Λ i h β) =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) ≫
        (probeOldBlockDot D Sc m i Λ h β).total (M β) ≫
          eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm := by
  change probeOldWeightDotComponent D Sc m i Λ h 0 M (blockSucc D Λ i h β) +
    probeOldWeightDotComponent D Sc m i Λ h 1 M (blockSucc D Λ i h β) = _
  rw [probeOldWeightDotComponent_blockSucc, probeOldWeightDotComponent_blockSucc]
  exact (conjugate_total (probeOldBlockInd D Sc m i Λ h β) (probeOldBlockDot D Sc m i Λ h β)
    (M β) (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M)).symm

/-- Every output block uses the actual inverse, including absent predecessors. -/
theorem probeOldActionDot_component_isUnit (M : ProbeOldWeightProduct D Sc m Λ x)
    (δ : WeightBlocks D Λ y) :
    IsUnit (End.of ((probeOldActionDot D Sc m i Λ h).total M δ)) := by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [probeOldActionDot_total_blockSucc]
    exact conjugate_unit (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) _
      (superfunctorEnd_total_isUnit (probeOldBlockInd D Sc m i Λ h β)
        (probeOldBlockDot D Sc m i Λ h β) (probeOldBlockDot_isUnit D Sc m i Λ h β) (M β))
  · have hz := probeOldInductionComponent_isZero D Sc m i Λ h δ hδ M
    rw [hz.eq_of_src ((probeOldActionDot D Sc m i Λ h).total M δ) (𝟙 _)]
    exact isUnit_one

/-- The actual dot has a natural inverse over an arbitrary original-weight fibre. -/
def probeOldActionDotIso : probeOldE D Sc m i Λ h ≅ probeOldE D Sc m i Λ h :=
  homogeneousTotalUnitIso (probeOldE D Sc m i Λ h) (probeOldActionDot D Sc m i Λ h)
    (probeOldActionDot_mem D Sc m i Λ h) (fun M =>
      productEnd_isUnit (fun δ : WeightBlocks D Λ y => ProbeCanonicalModules D Sc m δ.1)
        ((probeOldE D Sc m i Λ h).obj M) ((probeOldActionDot D Sc m i Λ h).total M)
        (probeOldActionDot_component_isUnit D Sc m i Λ h M))

@[simp] theorem probeOldActionDotIso_hom :
    (probeOldActionDotIso D Sc m i Λ h).hom = probeOldActionDot D Sc m i Λ h :=
  homogeneousTotalUnitIso_hom _ _ _ _

/-- Whole natural invertibility of the prescribed signed probe dot. -/
theorem probeOldActionDot_isUnit : IsUnit (End.of (probeOldActionDot D Sc m i Λ h)) := by
  apply (isUnit_iff_isIso _).mpr
  rw [← probeOldActionDotIso_hom]
  infer_instance

end OddMath.QuiverHecke
