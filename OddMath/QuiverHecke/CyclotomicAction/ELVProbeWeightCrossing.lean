/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPairInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridCrossSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAffineRelations

/-! # The prescribed equal crossing on OLD probe weight induction

Brundan–Ellis Definition 1.5, (1.7): lift the chosen negative double
crossing to the actual original-weight OLD probe functors. Every supported
coordinate retains its two stored-target append functors and their literal
balanced flattening. Absent double predecessors act on the actual zero
module. There is no coefficient-power quotient or comparison hypothesis.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u v w t z

private def crossingTransport
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} (h : F = G) (f : SuperNatTrans k G G) : SuperNatTrans k F F := by
  cases h
  exact f

private theorem crossingTransport_homogeneous
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} (h : F = G) (f : SuperNatTrans k G G) {p : ZMod 2}
    (hf : f.IsHomogeneous p) : (crossingTransport h f).IsHomogeneous p := by
  cases h
  exact hf

private theorem crossingTransport_component
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} (h : F = G) (f : SuperNatTrans k G G) (p : ZMod 2) (M : C) :
    (crossingTransport h f).app p M =
      eqToHom (congrArg (fun H : C ⥤ A => H.obj M) h) ≫ f.app p M ≫
        eqToHom (congrArg (fun H : C ⥤ A => H.obj M) h).symm := by
  cases h
  simp only [crossingTransport, eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem crossingTransport_total
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} (h : F = G) (f : SuperNatTrans k G G) (M : C) :
    (crossingTransport h f).total M =
      eqToHom (congrArg (fun H : C ⥤ A => H.obj M) h) ≫ f.total M ≫
        eqToHom (congrArg (fun H : C ⥤ A => H.obj M) h).symm := by
  cases h
  simp only [crossingTransport, eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

local notation "J" β => probeOldBlockAppend D Sc m i Λ h₁ β
local notation "K" β => probeOldBlockAppend D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)

/-- The literal OLD crossing at the two actual stored-target appends. -/
def probeOldBlockEqualCrossArrow (β : WeightBlocks D Λ x₀)
    (s : OldContentCategory D Sc (probeCutoff D m) β.1.toList) :
    ((J β) ⋙ (K β)).obj s ⟶ ((J β) ⋙ (K β)).obj s :=
  CyclotomicCrossingTensor.equalCrossComponent D Sc (probeCutoff D m) i s.obj

theorem probeOldBlockEqualCrossArrow_supernatural (β : WeightBlocks D Λ x₀) :
    IsSupernatural k (D.parity i) (probeOldBlockEqualCrossArrow D Sc m i Λ h₁ h₂ β) := by
  have h : IsSupernatural k (D.parity i * D.parity i)
      (probeOldBlockEqualCrossArrow D Sc m i Λ h₁ h₂ β) := {
    mem := fun s => (CyclotomicCrossingTensor.equalCross_supernatural D Sc (probeCutoff D m) i).mem s.obj
    naturality := fun hf =>
      (CyclotomicCrossingTensor.equalCross_supernatural D Sc (probeCutoff D m) i).naturality hf }
  simpa only [SKM.zmod2_mul_self] using h

local notation "hc" β => probeOldBlockEqualCrossArrow_supernatural D Sc m i Λ h₁ h₂ β

private theorem probeOldBlockPair_closed (β : WeightBlocks D Λ x₀)
    (M : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) β.1.toList) (SVec k))
    (hM : ProbeEvaluatesCoefficients D m Sc β.1.toList M) :
    ProbeEvaluatesCoefficients D m Sc (blockSucc₂ D i i Λ h₁ h₂ β).1.toList
      (((inductionModuleCell (k := k) (J β)) ≫ inductionModuleCell (k := k) (K β)).obj M) :=
  ((probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β).obj ⟨M, hM⟩).property

/-- The homogeneous chosen crossing of the prescribed block pair. -/
def probeOldBlockEqualCross (β : WeightBlocks D Λ x₀) :
    End (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) :=
  fullLiftTrans (ProbeEvaluatesCoefficients D m Sc β.1.toList)
    (ProbeEvaluatesCoefficients D m Sc (blockSucc₂ D i i Λ h₁ h₂ β).1.toList)
    (probeOldBlockPair_closed D Sc m i Λ h₁ h₂ β)
    (probeOldBlockPair_closed D Sc m i Λ h₁ h₂ β)
    (inductionModuleCross (J β) (K β) (hc β))

theorem probeOldBlockEqualCross_mem (β : WeightBlocks D Λ x₀) :
    probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous (ProbeEvaluatesCoefficients D m Sc β.1.toList)
      (ProbeEvaluatesCoefficients D m Sc (blockSucc₂ D i i Λ h₁ h₂ β).1.toList)
      (probeOldBlockPair_closed D Sc m i Λ h₁ h₂ β)
      (probeOldBlockPair_closed D Sc m i Λ h₁ h₂ β)
      (inductionModuleCross (J β) (K β) (hc β))
      (Superfunctor.mem_parity_iff_isHomogeneous.mp
        (inductionModuleCross_mem (J β) (K β) (hc β))))

/-- Forgetting only scalar-evaluation certificates retains the literal OLD crossing. -/
theorem probeOldBlockEqualCross_native_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom =
      (inductionModuleCross (J β) (K β) (hc β)).total M.obj := rfl

/-- The selected stored-target block crossing is square-zero. -/
theorem probeOldBlockEqualCross_square (β : WeightBlocks D Λ x₀) :
    probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β ≫
      probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β = 0 := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom ≫
    ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom = 0
  simp only [probeOldBlockEqualCross_native_total]
  rw [← Superfunctor.comp_total, inductionModuleCross_square (J β) (K β) (hc β)
    (fun s => oldContentEqualCross_square D Sc (probeCutoff D m) β.1.toList i s)]
  rfl

/-- Global coordinate transport retains the chosen pair of actual predecessors. -/
def probeOldWeightEqualCrossVia (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₂) (hε : blockSucc₂ D i i Λ h₁ h₂ β = ε) :
    SuperNatTrans k
      (probeOldEFunctor D Sc m i Λ h₁ ⋙ (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor)
      (probeOldEFunctor D Sc m i Λ h₁ ⋙ (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor) := by
  subst ε
  exact crossingTransport (probeOldEFunctor_comp₂_blockSucc D Sc m i i Λ h₁ h₂ β)
    (Superfunctor.whiskerLeft (probeOldBlockEval D Sc m Λ β)
      (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β))

theorem probeOldWeightEqualCrossVia_homogeneous (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₂) (hε : blockSucc₂ D i i Λ h₁ h₂ β = ε) :
    (probeOldWeightEqualCrossVia D Sc m i Λ h₁ h₂ β ε hε).IsHomogeneous (D.parity i) := by
  subst ε
  exact crossingTransport_homogeneous _ _
    (Superfunctor.mem_parity_iff_isHomogeneous.1
      (Superfunctor.whiskerLeft_mem (probeOldBlockEval D Sc m Λ β)
        (probeOldBlockEqualCross_mem D Sc m i Λ h₁ h₂ β)))

/-- The supported global coordinate equals the literal stored-target block pair. -/
theorem probeOldWeightPair_obj_eq (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldEFunctor D Sc m i Λ h₁ ⋙
      (probeOldInductionComponent D Sc m i Λ h₂ (blockSucc₂ D i i Λ h₁ h₂ β)).toFunctor).obj M =
      (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β).obj (M β) :=
  congrArg (fun H => H.obj M) (probeOldEFunctor_comp₂_blockSucc D Sc m i i Λ h₁ h₂ β)

/-- The whole supported crossing is conjugation by the selected coordinate equality. -/
theorem probeOldWeightEqualCrossVia_component (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldWeightEqualCrossVia D Sc m i Λ h₁ h₂ β (blockSucc₂ D i i Λ h₁ h₂ β) rfl).app p M =
      eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) ≫
        (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).app p (M β) ≫
          eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M).symm :=
  crossingTransport_component _ _ p M

/-- Total evaluation uses exactly the same selected stored-target coordinate map. -/
theorem probeOldWeightEqualCrossVia_total (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldWeightEqualCrossVia D Sc m i Λ h₁ h₂ β (blockSucc₂ D i i Λ h₁ h₂ β) rfl).total M =
      eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) ≫
        (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β) ≫
          eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M).symm :=
  crossingTransport_total _ _ M

theorem probeOldWeightEqualCrossVia_eq (β β' : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₂) (hε : blockSucc₂ D i i Λ h₁ h₂ β = ε)
    (hε' : blockSucc₂ D i i Λ h₁ h₂ β' = ε) :
    probeOldWeightEqualCrossVia D Sc m i Λ h₁ h₂ β ε hε =
      probeOldWeightEqualCrossVia D Sc m i Λ h₁ h₂ β' ε hε' := by
  obtain rfl := blockSucc₂_injective D i i Λ h₁ h₂ (hε.trans hε'.symm)
  rfl

/-- The crossing is zero precisely on the specified absent double-predecessor branch. -/
def probeOldWeightEqualCrossComponent (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) (ε : WeightBlocks D Λ x₂) :
    (probeOldEFunctor D Sc m i Λ h₁ ⋙
        (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor).obj M ⟶
      (probeOldEFunctor D Sc m i Λ h₁ ⋙
        (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor).obj M :=
  if hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε then
    (probeOldWeightEqualCrossVia D Sc m i Λ h₁ h₂ hε.choose ε hε.choose_spec).app p M
  else 0

theorem probeOldWeightEqualCrossComponent_of (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₂) (hε : blockSucc₂ D i i Λ h₁ h₂ β = ε) :
    probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ p M ε =
      (probeOldWeightEqualCrossVia D Sc m i Λ h₁ h₂ β ε hε).app p M := by
  unfold probeOldWeightEqualCrossComponent
  split
  · rename_i hchoice
    rw [probeOldWeightEqualCrossVia_eq D Sc m i Λ h₁ h₂ hchoice.choose β ε hchoice.choose_spec hε]
  · rename_i hnot
    exact absurd (⟨β, hε⟩ : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε) hnot

theorem probeOldWeightEqualCrossComponent_absent (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) (ε : WeightBlocks D Λ x₂)
    (hε : ¬ ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε) :
    probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ p M ε = 0 := by
  simp only [probeOldWeightEqualCrossComponent, dite_eq_right hε]

theorem probeOldWeightEqualCrossComponent_mem (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) (ε : WeightBlocks D Λ x₂) :
    probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ p M ε ∈ parity (R := k) _ _ p := by
  unfold probeOldWeightEqualCrossComponent
  split
  · exact SuperNatTrans.app_mem _ p M
  · exact Submodule.zero_mem _

theorem probeOldWeightEqualCrossComponent_naturality (p : ZMod 2) (ε : WeightBlocks D Λ x₂)
    {M M' : ProbeOldWeightProduct D Sc m Λ x₀} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (probeOldEFunctor D Sc m i Λ h₁ ⋙
        (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor).map f ≫
        probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ p M' ε =
      koszulSign p q • (probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ p M ε ≫
        (probeOldEFunctor D Sc m i Λ h₁ ⋙
          (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor).map f) := by
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldWeightEqualCrossComponent_of D Sc m i Λ h₁ h₂ p M β ε hβ,
      probeOldWeightEqualCrossComponent_of D Sc m i Λ h₁ h₂ p M' β ε hβ]
    exact (probeOldWeightEqualCrossVia D Sc m i Λ h₁ h₂ β ε hβ).naturality p f hf
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i i Λ h₁ h₂ ε hε M).eq_of_src _ _

/-- The prescribed negative equal crossing of the actual global OLD probe induction. -/
def probeOldWeightEqualCross :
    SuperNatTrans k
      (probeOldEFunctor D Sc m i Λ h₁ ⋙ probeOldEFunctor D Sc m i Λ h₂)
      (probeOldEFunctor D Sc m i Λ h₁ ⋙ probeOldEFunctor D Sc m i Λ h₂) where
  app p M ε := probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ p M ε
  app_mem p M ε := probeOldWeightEqualCrossComponent_mem D Sc m i Λ h₁ h₂ p M ε
  naturality p _ _ _ f hf := funext fun ε =>
    probeOldWeightEqualCrossComponent_naturality D Sc m i Λ h₁ h₂ p ε f hf

theorem probeOldWeightEqualCross_homogeneous :
    (probeOldWeightEqualCross D Sc m i Λ h₁ h₂).IsHomogeneous (D.parity i) := by
  intro q hq
  funext M ε
  change probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ q M ε = 0
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldWeightEqualCrossComponent_of D Sc m i Λ h₁ h₂ q M β ε hβ]
    exact congrFun (probeOldWeightEqualCrossVia_homogeneous D Sc m i Λ h₁ h₂ β ε hβ q hq) M
  · exact probeOldWeightEqualCrossComponent_absent D Sc m i Λ h₁ h₂ q M ε hε

/-- The total global crossing retains the entire chosen supported component. -/
theorem probeOldWeightEqualCross_total_of (M : ProbeOldWeightProduct D Sc m Λ x₀)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₂)
    (hε : blockSucc₂ D i i Λ h₁ h₂ β = ε) :
    (probeOldWeightEqualCross D Sc m i Λ h₁ h₂).total M ε =
      (probeOldWeightEqualCrossVia D Sc m i Λ h₁ h₂ β ε hε).total M := by
  change probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ 0 M ε +
    probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ 1 M ε = _
  rw [probeOldWeightEqualCrossComponent_of D Sc m i Λ h₁ h₂ 0 M β ε hε,
    probeOldWeightEqualCrossComponent_of D Sc m i Λ h₁ h₂ 1 M β ε hε]
  rfl

/-- The equal crossing as an action-target two-morphism. -/
def probeOldActionEqualCross :
    probeOldE D Sc m i Λ h₁ ≫ probeOldE D Sc m i Λ h₂ ⟶
      probeOldE D Sc m i Λ h₁ ≫ probeOldE D Sc m i Λ h₂ :=
  probeOldWeightEqualCross D Sc m i Λ h₁ h₂

theorem probeOldActionEqualCross_mem :
    probeOldActionEqualCross D Sc m i Λ h₁ h₂ ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.2
    (probeOldWeightEqualCross_homogeneous D Sc m i Λ h₁ h₂)

/-- The chosen global equal crossing is square-zero on every OLD probe input. -/
theorem probeOldActionEqualCross_square :
    probeOldActionEqualCross D Sc m i Λ h₁ h₂ ≫
      probeOldActionEqualCross D Sc m i Λ h₁ h₂ = 0 := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total]
  simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add]
  funext ε
  change (probeOldWeightEqualCross D Sc m i Λ h₁ h₂).total M ε ≫
    (probeOldWeightEqualCross D Sc m i Λ h₁ h₂).total M ε = 0
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    rw [probeOldWeightEqualCross_total_of D Sc m i Λ h₁ h₂ M β _ rfl,
      probeOldWeightEqualCrossVia_total]
    have hs := congrArg
      (fun f : End (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) => f.total (M β))
      (probeOldBlockEqualCross_square D Sc m i Λ h₁ h₂ β)
    have hs' : (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β) ≫
        (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β) = 0 := by
      rw [Superfunctor.comp_total] at hs
      simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add] using hs
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β)), hs']
    simp only [Limits.zero_comp, Limits.comp_zero]
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i i Λ h₁ h₂ ε hε M).eq_of_src _ _

end OddMath.QuiverHecke
