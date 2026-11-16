import OddMath.QuiverHecke.CyclotomicAction.ProbeCap
import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier
import OddMath.QuiverHecke.CyclotomicAction.ContentHom
import OddMath.QuiverHecke.CyclotomicAction.AppendSourceRows
import OddMath.QuiverHecke.CyclotomicAction.ProbeMixed
import OddMath.QuiverHecke.CyclotomicAction.ContentAppend
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed
import OddMath.QuiverHecke.CyclotomicAction.WeightMixed
import OddMath.QuiverHecke.SwappedAssembly.ProductDenominatorUnits

/-!
# Probe weight dot

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
open ELV ELV.BalancedInduction CyclotomicAction
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
theorem probeOldBlockEqualCross_total (β : WeightBlocks D Λ x₀)
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
  simp only [probeOldBlockEqualCross_total]
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
end

end

section

/-! # The chosen OLD probe block braid

Brundan–Ellis (1.9): the independent chosen negative crossings on three
actual stored-target probe block inductions satisfy the braid. The literal
OLD source braid supplies the input to the changing-category induction grid;
no braid, comparison or scalar-specialization faithfulness premise is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u v w z t

private theorem braid_whiskerRight_total
    {k : Type u} [CommRing k] {C A B : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{t} B] [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C A} (x : F ⟶ G) (H : Superfunctor k A B) (M : C) :
    (Superfunctor.whiskerRight x H).total M = H.map (x.total M) := by
  change H.map (x.app 0 M) + H.map (x.app 1 M) = H.map (x.app 0 M + x.app 1 M)
  exact H.toFunctor.map_add.symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
local notation "J" β => probeOldBlockAppend D Sc m i Λ h₁ β
local notation "K" β => probeOldBlockAppend D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "L" β => probeOldBlockAppend D Sc m i Λ h₃ (blockSucc₂ D i i Λ h₁ h₂ β)
local notation "hγ" β => probeOldBlockEqualCrossArrow_supernatural D Sc m i Λ h₁ h₂ β
local notation "hδ" β => probeOldBlockEqualCrossArrow_supernatural D Sc m i Λ h₂ h₃ (blockSucc D Λ i h₁ β)

/-- The chosen first pair crossing, mapped by the actual third block induction. -/
abbrev probeOldBlockBraidPrefix (β : WeightBlocks D Λ x₀) :
    End (probeOldBlockTripleInd D Sc m i i i Λ h₁ h₂ h₃ β) :=
  Superfunctor.whiskerRight (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β)
    (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D i i Λ h₁ h₂ β))

/-- The independently chosen second pair crossing, after the first block induction. -/
abbrev probeOldBlockBraidSuffix (β : WeightBlocks D Λ x₀) :
    End (probeOldBlockTripleInd D Sc m i i i Λ h₁ h₂ h₃ β) :=
  Superfunctor.whiskerLeft (probeOldBlockInd D Sc m i Λ h₁ β)
    (probeOldBlockEqualCross D Sc m i Λ h₂ h₃ (blockSucc D Λ i h₁ β))

theorem probeOldBlockBraidPrefix_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total M =
      (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D i i Λ h₁ h₂ β)).map
        ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M) :=
  braid_whiskerRight_total _ _ M

theorem probeOldBlockBraidSuffix_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total M =
      (probeOldBlockEqualCross D Sc m i Λ h₂ h₃ (blockSucc D Λ i h₁ β)).total
        ((probeOldBlockInd D Sc m i Λ h₁ β).obj M) := rfl

/-- The first chosen block crossing whiskering retains its entire OLD module map. -/
theorem probeOldBlockBraidPrefix_direct_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total M).hom =
      (induction (L β)).map ((inductionModuleCross (J β) (K β) (hγ β)).total M.obj) := by
  rw [probeOldBlockBraidPrefix_total]
  change (induction (L β)).map (((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom) = _
  rw [probeOldBlockEqualCross_total]

/-- The second chosen block crossing retains the exact OLD pair crossing at its true input. -/
theorem probeOldBlockBraidSuffix_direct_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total M).hom =
      (inductionModuleCross (K β) (L β) (hδ β)).total ((induction (J β)).obj M.obj) := by
  rw [probeOldBlockBraidSuffix_total, probeOldBlockEqualCross_total]
  rfl

/-- The given negative block crossings satisfy the braid on all evaluated inputs. -/
theorem probeOldBlockEqualCross_braid (β : WeightBlocks D Λ x₀) :
    probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β ≫
      probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β ≫
        probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β =
    probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β ≫
      probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β ≫
        probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    Superfunctor.comp_total, Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change ((probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total M).hom ≫
      ((probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total M).hom ≫
        ((probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total M).hom =
    ((probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total M).hom ≫
      ((probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total M).hom ≫
        ((probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total M).hom
  rw [probeOldBlockBraidPrefix_direct_total, probeOldBlockBraidSuffix_direct_total]
  exact (inductionModuleCross_braid (J β) (K β) (L β) (hγ β) (hδ β)
    (fun s => CyclotomicCrossingTensor.equalCrossComponent_braid D Sc (probeCutoff D m) i s.obj) M.obj).symm

end OddMath.QuiverHecke
end

end

section

/-! # The equal-colour braid on the entire OLD probe weight category

Brundan–Ellis (1.9): compare the two actual crossing whiskerings through
one selected triple-coordinate equality. The direct stored-target OLD
block braid supplies the relation. No braid, comparison, inversion or
finite-weight-fibre premise is introduced; absent coordinates are zero.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u v w z

private theorem braid_prefix_conjugate
    {C A : Type v} [Category.{w} C] [Category.{z} A]
    (G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V : A}
    (hV : V = G.obj M₀) (hW : V = G.obj M₁) (d : End M₁) :
    eqToHom hV ≫ G.map (eqToHom hM ≫ d ≫ eqToHom hM.symm) ≫ eqToHom hV.symm =
      eqToHom hW ≫ G.map d ≫ eqToHom hW.symm := by
  cases hM
  cases hV
  cases hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem braid_suffix_conjugate
    {k : Type u} [CommRing k] {C A : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V : A}
    (hV : V = G.obj M₀) (hW : V = G.obj M₁) (d : SuperNatTrans k G G) :
    eqToHom hV ≫ d.total M₀ ≫ eqToHom hV.symm =
      eqToHom hW ≫ d.total M₁ ≫ eqToHom hW.symm := by
  cases hM
  cases hV
  cases hW
  rfl

private theorem conjugate_braid {C : Type v} [Category.{w} C]
    {A B : C} (e : A = B) (a b : End B)
    (hb : b ≫ a ≫ b = a ≫ b ≫ a) :
    (eqToHom e ≫ b ≫ eqToHom e.symm) ≫ (eqToHom e ≫ a ≫ eqToHom e.symm) ≫
        (eqToHom e ≫ b ≫ eqToHom e.symm) =
      (eqToHom e ≫ a ≫ eqToHom e.symm) ≫ (eqToHom e ≫ b ≫ eqToHom e.symm) ≫
        (eqToHom e ≫ a ≫ eqToHom e.symm) := by
  cases e
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hb

private theorem reassociated_probePrefix_total
    {k : Type u} [CommRing k] {A B C E : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ E) (x : F ≫ G ⟶ F ≫ G) (M : A) :
    ((associator F G H).inv ≫ x ▷ H ≫ (associator F G H).hom).total M = H.map (x.total M) := by
  erw [PiSCat.associator_inv, PiSCat.associator_hom, Category.id_comp, Category.comp_id]
  change H.map (x.app 0 M) + H.map (x.app 1 M) = H.map (x.app 0 M + x.app 1 M)
  exact H.toFunctor.map_add.symm

private theorem braid_total_three
    {k : Type u} [CommRing k] {C A : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (F : Superfunctor k C A) (f g h : End F) (M : C) :
    (f ≫ g ≫ h).total M = f.total M ≫ g.total M ≫ h.total M := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
local notation "E₁" => probeOldE D Sc m i Λ h₁
local notation "E₂" => probeOldE D Sc m i Λ h₂
local notation "E₃" => probeOldE D Sc m i Λ h₃

/-- The actual first pair crossing in the prescribed right-associated triple. -/
abbrev probeOldWeightBraidPrefix : End (E₁ ≫ E₂ ≫ E₃) :=
  (associator E₁ E₂ E₃).inv ≫
    probeOldActionEqualCross D Sc m i Λ h₁ h₂ ▷ E₃ ≫ (associator E₁ E₂ E₃).hom

/-- The independently chosen second pair crossing, after the actual first induction. -/
abbrev probeOldWeightBraidSuffix : End (E₁ ≫ E₂ ≫ E₃) :=
  E₁ ◁ probeOldActionEqualCross D Sc m i Λ h₂ h₃

theorem probeOldWeightBraidPrefix_total (M : ProbeOldWeightProduct D Sc m Λ x₀)
    (ε : WeightBlocks D Λ x₃) :
    (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃).total M ε =
      (probeOldInductionComponent D Sc m i Λ h₃ ε).map
        ((probeOldActionEqualCross D Sc m i Λ h₁ h₂).total M) :=
  congrFun (reassociated_probePrefix_total E₁ E₂ E₃
    (probeOldActionEqualCross D Sc m i Λ h₁ h₂) M) ε

theorem probeOldWeightBraidSuffix_total (M : ProbeOldWeightProduct D Sc m Λ x₀)
    (ε : WeightBlocks D Λ x₃) :
    (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃).total M ε =
      (probeOldActionEqualCross D Sc m i Λ h₂ h₃).total ((E₁).obj M) ε := rfl

/-- The actual first crossing uses the selected triple coordinate and prescribed block map. -/
theorem probeOldWeightBraidPrefix_component (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃).total M
        (probeOldBlockSucc₃ D i i i Λ h₁ h₂ h₃ β) =
      eqToHom (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M) ≫
        (probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total (M β) ≫
        eqToHom (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M).symm := by
  rw [probeOldWeightBraidPrefix_total, probeOldInductionComponent_map_blockSucc]
  simp only [probeOldActionEqualCross]
  rw [probeOldWeightEqualCross_total_of D Sc m i Λ h₁ h₂ M β _ rfl,
    probeOldWeightEqualCrossVia_total, probeOldBlockBraidPrefix_total]
  have ht := braid_prefix_conjugate
    (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D i i Λ h₁ h₂ β)).toFunctor
    (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M)
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₃ (blockSucc₂ D i i Λ h₁ h₂ β)
      ((E₁ ≫ E₂).obj M))
    (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M)
    ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β))
  convert! ht using 1

/-- The independently chosen second crossing uses that identical triple coordinate. -/
theorem probeOldWeightBraidSuffix_component (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃).total M
        (probeOldBlockSucc₃ D i i i Λ h₁ h₂ h₃ β) =
      eqToHom (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M) ≫
        (probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total (M β) ≫
        eqToHom (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M).symm := by
  rw [probeOldWeightBraidSuffix_total]
  simp only [probeOldActionEqualCross]
  rw [probeOldWeightEqualCross_total_of D Sc m i Λ h₂ h₃ ((E₁).obj M)
      (blockSucc D Λ i h₁ β) _ rfl,
    probeOldWeightEqualCrossVia_total, probeOldBlockBraidSuffix_total]
  have ht := braid_suffix_conjugate
    (probeOldBlockPairInd D Sc m i i Λ h₂ h₃ (blockSucc D Λ i h₁ β)).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₁ β M)
    (probeOldWeightPair_obj_eq D Sc m i Λ h₂ h₃ (blockSucc D Λ i h₁ β) ((E₁).obj M))
    (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M)
    (probeOldBlockEqualCross D Sc m i Λ h₂ h₃ (blockSucc D Λ i h₁ β))
  exact ht

/-- The prescribed equal crossings satisfy the whole-weight OLD probe braid. -/
theorem probeOldActionEqualCross_braid :
    probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃ ≫
      probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃ ≫
        probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃ =
    probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃ ≫
      probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃ ≫
        probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃ := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  funext ε
  have hL := congrFun (braid_total_three (E₁ ≫ E₂ ≫ E₃)
    (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃)
    (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃)
    (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃) M) ε
  have hR := congrFun (braid_total_three (E₁ ≫ E₂ ≫ E₃)
    (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃)
    (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃)
    (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃) M) ε
  apply hL.trans
  apply Eq.trans _ hR.symm
  by_cases hε : ∃ β, probeOldBlockSucc₃ D i i i Λ h₁ h₂ h₃ β = ε
  · obtain ⟨β, rfl⟩ := hε
    change (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃).total M _ ≫
        (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃).total M _ ≫
          (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃).total M _ =
      (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃).total M _ ≫
        (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃).total M _ ≫
          (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃).total M _
    rw [probeOldWeightBraidPrefix_component, probeOldWeightBraidSuffix_component]
    have hb := congrArg
      (fun f : End (probeOldBlockTripleInd D Sc m i i i Λ h₁ h₂ h₃ β) => f.total (M β))
      (probeOldBlockEqualCross_braid D Sc m i Λ h₁ h₂ h₃ β)
    rw [Superfunctor.comp_total, Superfunctor.comp_total,
      Superfunctor.comp_total, Superfunctor.comp_total] at hb
    have ht := conjugate_braid (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M)
      ((probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total (M β))
      ((probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total (M β)) hb
    convert! ht using 1
  · exact (probeOldEFunctor_comp₃_isZero D Sc m i i i Λ h₁ h₂ h₃ ε hε M).eq_of_src _ _

end OddMath.QuiverHecke
end

end

section

/-! # Whole signed dot unit on the evaluated old probe category

`SwappedNondegeneracy` §3 and `SwappedActionAssembly` F2 require a natural
probe-dot inverse on the actual factor category. The full scalar-evaluated
old module subcategory supplies the actual algebra-quotient inverse for
every object. Pointwise homogeneous inverses assemble into an isomorphism
of the prescribed induction superfunctor, including odd colour parity.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
private theorem transform_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ J.obj v} (hα : IsSupernatural k p α)
    (N : Superfunctor k C (SVec k)) (t : A) :
    (transformComponent hα N).total t = transformLinear hα N t := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc (probeCutoff D m) ν i
local notation "hDot" => probeOldContentAppendDot_supernatural D Sc m ν i
local notation "E" => probeEvaluatedInduction D Sc m ν i

/-- The chosen signed dot, retaining its whole module morphism. -/
def probeEvaluatedDotComponent (N : ProbeEvaluatedModules D Sc m ν) :
    (E).obj N ⟶ (E).obj N := ⟨transformComponent hDot N.obj⟩

theorem probeEvaluatedDotComponent_supernatural :
    IsSupernatural k (D.parity i) (F := E) (G := E)
      (probeEvaluatedDotComponent D Sc m ν i) where
  mem N := transformComponent_mem hDot N.obj
  naturality := by
    intro M N p f hf
    apply InducedCategory.hom_ext
    change f.hom ∈ parity (R := k) _ _ p at hf
    exact (transformComponent_supernatural hDot).naturality hf

/-- The whole signed dot on the actual evaluated induction functor. -/
def probeEvaluatedInductionDot :
    End (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: ν))) :=
  (probeEvaluatedDotComponent_supernatural D Sc m ν i).toSuperNatTrans

theorem probeEvaluatedInductionDot_mem :
    probeEvaluatedInductionDot D Sc m ν i ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem
    (probeEvaluatedDotComponent_supernatural D Sc m ν i)

/-- The whole functor dot has exactly the prescribed native module component. -/
theorem probeEvaluatedInductionDot_total (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedInductionDot D Sc m ν i).total N = probeEvaluatedDotComponent D Sc m ν i N :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m (i :: ν))))
    (G := (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m (i :: ν))))
    (probeEvaluatedDotComponent_supernatural D Sc m ν i) N

variable [Fintype I]

/-- Every evaluated old probe module has the prescribed dot isomorphism;
the inverse comes from the actual scalar quotient, with no inverse premise. -/
def probeEvaluatedDotModuleIso [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    induced J N.obj ≅ induced J N.obj :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals
    (transformComponent hDot N.obj) (transformComponent_mem hDot N.obj) (by
      intro t
      rw [transform_total]
      change Function.Bijective (probeOldContentInductionDot D Sc m ν i N.obj t)
      have h := probeOldContentInductionDot_isUnit D Sc m ν i N.obj N.property t
      exact (Module.End.isUnit_iff _).mp h)

/-- The dot isomorphism retains the exact specified module forward. -/
theorem probeEvaluatedDotModuleIso_hom [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedDotModuleIso D Sc m ν i N).hom = transformComponent hDot N.obj :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals_hom _ _ _

/-- The pointwise inverse is a morphism of the same full evaluated category. -/
def probeEvaluatedDotIso [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) : (E).obj N ≅ (E).obj N :=
  ObjectProperty.isoMk (ProbeEvaluatesCoefficients D m Sc (i :: ν)) (probeEvaluatedDotModuleIso D Sc m ν i N)

private theorem evaluatedDotIso_hom_total [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedDotIso D Sc m ν i N).hom = (probeEvaluatedInductionDot D Sc m ν i).total N := by
  rw [probeEvaluatedInductionDot_total]
  apply InducedCategory.hom_ext
  exact probeEvaluatedDotModuleIso_hom D Sc m ν i N

/-- The actual dot inverse is natural on the entire evaluated probe category. -/
def probeEvaluatedInductionDotIso [Fact Sc.PureNilpotent] :
    (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: ν))) ≅ ⟨E⟩ :=
  OddMath.HomogeneousSuperfunctorIso.ofHom
    (probeEvaluatedInductionDot D Sc m ν i) (probeEvaluatedInductionDot_mem D Sc m ν i)
    (probeEvaluatedDotIso D Sc m ν i) (evaluatedDotIso_hom_total D Sc m ν i)

@[simp] theorem probeEvaluatedInductionDotIso_hom [Fact Sc.PureNilpotent] :
    (probeEvaluatedInductionDotIso D Sc m ν i).hom = probeEvaluatedInductionDot D Sc m ν i :=
  OddMath.HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

end OddMath.QuiverHecke
end

end

section

/-! # The prescribed right adjunction on evaluated old probes

For SwappedActionAssembly F1–F2 and BE (1.10), restrict the actual balanced
unit and counit to the scalar-evaluated full categories. Their evenness
and both triangles are inherited. The whole dot unit retains the existing
native old-content induction dot, with no change of sign or adjunction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc (probeCutoff D m) ν i
local notation "E" => probeEvaluatedInduction D Sc m ν i
local notation "F" => probeEvaluatedRestriction D Sc m ν i

/-- The same chosen balanced unit, on the full evaluated subcategory. -/
def probeEvaluatedUnit : 𝟭 (ProbeEvaluatedModules D Sc m ν) ⟶ E ⋙ F where
  app N := ⟨(adjunction J).unit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).unit.naturality f.hom)

/-- The same chosen multiplication counit, with every module map retained. -/
def probeEvaluatedCounit : F ⋙ E ⟶ 𝟭 (ProbeEvaluatedModules D Sc m (i :: ν)) where
  app N := ⟨(adjunction J).counit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).counit.naturality f.hom)

/-- Restrict the actual right adjunction; both triangle identities are inherited. -/
def probeEvaluatedAdjunction : E ⊣ F where
  unit := probeEvaluatedUnit D Sc m ν i
  counit := probeEvaluatedCounit D Sc m ν i
  left_triangle_components N := InducedCategory.hom_ext ((adjunction J).left_triangle_components N.obj)
  right_triangle_components N := InducedCategory.hom_ext ((adjunction J).right_triangle_components N.obj)

theorem probeEvaluatedAdjunction_unit_mem (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedAdjunction D Sc m ν i).unit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionUnit_mem J N.obj

theorem probeEvaluatedAdjunction_counit_mem (N : ProbeEvaluatedModules D Sc m (i :: ν)) :
    (probeEvaluatedAdjunction D Sc m ν i).counit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionCounit_mem J N.obj

/-- The actual evaluated module category in the target of the swapped factors. -/
abbrev probeEvaluatedTarget (ν : List I) : PiSCat.{u,u,u+1} k :=
  letI := probeEvaluatedPiSupercategory D Sc m ν
  PiSCat.of k (ProbeEvaluatedModules D Sc m ν)

abbrev probeEvaluatedE : probeEvaluatedTarget D Sc m ν ⟶ probeEvaluatedTarget D Sc m (i :: ν) := ⟨E⟩
abbrev probeEvaluatedF : probeEvaluatedTarget D Sc m (i :: ν) ⟶ probeEvaluatedTarget D Sc m ν := ⟨F⟩

/-- The right adjunction uses precisely the restricted native unit and counit. -/
def probeEvaluatedRightAdjunction :
    SKM.SuperAdjunction (k := k) (probeEvaluatedE D Sc m ν i) (probeEvaluatedF D Sc m ν i) :=
  ordinaryEvenSuperAdjunction (probeEvaluatedE D Sc m ν i) (probeEvaluatedF D Sc m ν i)
    (probeEvaluatedAdjunction D Sc m ν i) (probeEvaluatedAdjunction_unit_mem D Sc m ν i)
    (probeEvaluatedAdjunction_counit_mem D Sc m ν i)

end OddMath.QuiverHecke
end

end

section

/-! # The prescribed adjunction for stored OLD probe contents

SwappedActionAssembly F1–F2 and BE (1.10): the full evaluated append
and restriction functors retain their specified target permutation. The
right unit, counit, evenness and triangles are the actual balanced ones.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ)
local notation "J" => oldContentAppendTo D Sc (probeCutoff D m) ν i μ h
local notation "E" => probeEvaluatedAppendTo D Sc m ν i μ h
local notation "F" => probeEvaluatedRestrictTo D Sc m ν i μ h

/-- The same chosen balanced unit, on the full evaluated subcategory. -/
def probeAppendToUnit : 𝟭 (ProbeEvaluatedModules D Sc m ν) ⟶ E ⋙ F where
  app N := ⟨(adjunction J).unit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).unit.naturality f.hom)

/-- The same chosen multiplication counit, with every module map retained. -/
def probeAppendToCounit : F ⋙ E ⟶ 𝟭 (ProbeEvaluatedModules D Sc m μ) where
  app N := ⟨(adjunction J).counit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).counit.naturality f.hom)

/-- Restrict the actual right adjunction; both triangle identities are inherited. -/
def probeAppendToAdjunction : E ⊣ F where
  unit := probeAppendToUnit D Sc m ν i μ h
  counit := probeAppendToCounit D Sc m ν i μ h
  left_triangle_components N := InducedCategory.hom_ext ((adjunction J).left_triangle_components N.obj)
  right_triangle_components N := InducedCategory.hom_ext ((adjunction J).right_triangle_components N.obj)

theorem probeAppendToAdjunction_unit_mem (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToAdjunction D Sc m ν i μ h).unit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionUnit_mem J N.obj

theorem probeAppendToAdjunction_counit_mem (N : ProbeEvaluatedModules D Sc m μ) :
    (probeAppendToAdjunction D Sc m ν i μ h).counit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionCounit_mem J N.obj

abbrev probeAppendToE : probeEvaluatedTarget D Sc m ν ⟶ probeEvaluatedTarget D Sc m μ := ⟨E⟩
abbrev probeAppendToF : probeEvaluatedTarget D Sc m μ ⟶ probeEvaluatedTarget D Sc m ν := ⟨F⟩

/-- The right adjunction uses precisely the restricted native unit and counit. -/
def probeAppendToRightAdjunction :
    SKM.SuperAdjunction (k := k) (probeAppendToE D Sc m ν i μ h) (probeAppendToF D Sc m ν i μ h) :=
  ordinaryEvenSuperAdjunction (probeAppendToE D Sc m ν i μ h) (probeAppendToF D Sc m ν i μ h)
    (probeAppendToAdjunction D Sc m ν i μ h) (probeAppendToAdjunction_unit_mem D Sc m ν i μ h)
    (probeAppendToAdjunction_counit_mem D Sc m ν i μ h)

end OddMath.QuiverHecke
end

end

section

/-! # Positive distinct crossings on OLD probe weight spaces

Brundan–Ellis Definition 1.5, (1.7)–(1.9): construct the positive
distinct crossing on the actual weight-product induction functors. The
four append functors retain their canonical stored contents and common
upper target. Absent double predecessors contribute the actual zero map.
The distinct mate inverse is a separate transport obligation.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u v w t z

private def distinctTransport
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G F' G' : C ⥤ A} (hs : F = F') (ht : G = G')
    (f : SuperNatTrans k F' G') : SuperNatTrans k F G := by
  cases hs
  cases ht
  exact f

private theorem distinctTransport_homogeneous
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G F' G' : C ⥤ A} (hs : F = F') (ht : G = G')
    (f : SuperNatTrans k F' G') {p : ZMod 2} (hf : f.IsHomogeneous p) :
    (distinctTransport hs ht f).IsHomogeneous p := by
  cases hs
  cases ht
  exact hf

private theorem distinctTransport_component
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G F' G' : C ⥤ A} (hs : F = F') (ht : G = G')
    (f : SuperNatTrans k F' G') (p : ZMod 2) (N : C) :
    (distinctTransport hs ht f).app p N =
      eqToHom (congrArg (fun H : C ⥤ A => H.obj N) hs) ≫ f.app p N ≫
        eqToHom (congrArg (fun H : C ⥤ A => H.obj N) ht).symm := by
  cases hs
  cases ht
  simp only [distinctTransport, eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

section Pair
variable (i j : I) (Λ : X) {x₀ x₁ xu : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = xu)

/-- The common upper stored list carries the actual two-successor content. -/
theorem probeOldPairUpper_perm (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    (i :: (blockSucc D Λ j h₁ β).1.toList).Perm ε.1.toList := by
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.coe_toList]
  change {i} + ((blockSucc D Λ j h₁ β).1.toList : Multiset I) = ε.1
  rw [Multiset.coe_toList]
  exact congrArg Subtype.val hε

/-- The second OLD append retains the specified common upper target. -/
abbrev probeOldPairUpperAppend (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :=
  oldContentAppendTo D Sc (probeCutoff D m) (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
    (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)

/-- Both actual block inductions with their prescribed common upper list. -/
abbrev probeOldBlockPairIndTo (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :=
  (probeOldBlockInd D Sc m j Λ h₁ β).comp
    (⟨probeEvaluatedAppendTo D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
      (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)⟩ :
      Superfunctor k (ProbeCanonicalModules D Sc m (blockSucc D Λ j h₁ β).1)
        (ProbeCanonicalModules D Sc m ε.1))

/-- The global coordinate equals the specified stored-target block pair. -/
theorem probeOldEFunctor_comp₂_to (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldEFunctor D Sc m j Λ h₁ ⋙
        (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor =
      (probeOldBlockEval D Sc m Λ β).toFunctor ⋙
        (probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hε).toFunctor := by
  subst ε
  exact probeOldEFunctor_comp₂_blockSucc D Sc m i j Λ h₁ h₂ β
end Pair

section Crossing
variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄
local notation "J" => probeOldBlockAppend D Sc m i Λ h₃
local notation "K" => probeOldBlockAppend D Sc m j Λ h₁
local notation "L" => (fun β ε hε => probeOldPairUpperAppend D Sc m j i Λ h₃ h₄ β ε (sw hε))
local notation "U" => probeOldPairUpperAppend D Sc m i j Λ h₁ h₂

/-- The same positive OLD crossing, at all four canonical stored contents. -/
def probeOldBlockDistinctCrossArrow (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (s : OldContentCategory D Sc (probeCutoff D m) β.1.toList) :
    ((J β) ⋙ (L β ε hε)).obj s ⟶ ((K β) ⋙ (U β ε hε)).obj s :=
  Distinct.crossComponent D Sc (probeCutoff D m) j i s.obj

theorem probeOldBlockDistinctCrossArrow_supernatural (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    IsSupernatural k (D.parity i * D.parity j)
      (probeOldBlockDistinctCrossArrow D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) := by
  have h : IsSupernatural k (D.parity j * D.parity i)
      (probeOldBlockDistinctCrossArrow D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) := {
    mem := fun s => (Distinct.cross_supernatural D Sc (probeCutoff D m) j i).mem s.obj
    naturality := fun hf =>
      (Distinct.cross_supernatural D Sc (probeCutoff D m) j i).naturality hf }
  simpa only [mul_comm] using h
local notation "hc" =>
  probeOldBlockDistinctCrossArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄

private theorem blockDistinctSource_closed (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) β.1.toList) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc β.1.toList N) :
    ProbeEvaluatesCoefficients D m Sc ε.1.toList
      ((induction (K β) ⋙ induction (U β ε hε)).obj N) :=
  ((probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hε).obj ⟨N, hN⟩).property

private theorem blockDistinctTarget_closed (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) β.1.toList) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc β.1.toList N) :
    ProbeEvaluatesCoefficients D m Sc ε.1.toList
      ((induction (J β) ⋙ induction (L β ε hε)).obj N) :=
  ((probeOldBlockPairIndTo D Sc m j i Λ h₃ h₄ β ε (sw hε)).obj ⟨N, hN⟩).property

/-- The selected positive crossing of the two stored-target block pairs. -/
def probeOldBlockDistinctCross (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hε ⟶
      probeOldBlockPairIndTo D Sc m j i Λ h₃ h₄ β ε (sw hε) :=
  fullLiftTrans (ProbeEvaluatesCoefficients D m Sc β.1.toList)
    (ProbeEvaluatesCoefficients D m Sc ε.1.toList)
    (blockDistinctSource_closed D Sc m i j Λ h₁ h₂ β ε hε)
    (blockDistinctTarget_closed D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε)
    (rectangularCrossComponent_supernatural (J β) (K β) (L β ε hε) (U β ε hε)
      (hc β ε hε)).toSuperNatTrans

theorem probeOldBlockDistinctCross_mem (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous (ProbeEvaluatesCoefficients D m Sc β.1.toList)
      (ProbeEvaluatesCoefficients D m Sc ε.1.toList)
      (blockDistinctSource_closed D Sc m i j Λ h₁ h₂ β ε hε)
      (blockDistinctTarget_closed D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) _
      (rectangularCrossComponent_supernatural (J β) (K β) (L β ε hε) (U β ε hε)
        (hc β ε hε)).toSuperNatTrans_isHomogeneous)

/-- Each parity component retains the literal OLD positive rectangular crossing. -/
theorem probeOldBlockDistinctCross_app (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (p : ZMod 2) (N : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app p N).hom =
      (rectangularCrossComponent_supernatural (J β) (K β) (L β ε hε) (U β ε hε)
        (hc β ε hε)).toSuperNatTrans.app p N.obj := rfl

local notation "Fs" => (fun ε => probeOldEFunctor D Sc m j Λ h₁ ⋙
  Superfunctor.toFunctor (probeOldInductionComponent D Sc m i Λ h₂ ε))
local notation "Ft" => (fun ε => probeOldEFunctor D Sc m i Λ h₃ ⋙
  Superfunctor.toFunctor (probeOldInductionComponent D Sc m j Λ h₄ ε))

/-- Transport the constructed block crossing through both actual product coordinates. -/
def probeOldWeightDistinctCrossVia (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) : SuperNatTrans k (Fs ε) (Ft ε) :=
  distinctTransport (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε)
    (probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε (sw hε))
    (Superfunctor.whiskerLeft (probeOldBlockEval D Sc m Λ β)
      (probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε))

theorem probeOldWeightDistinctCrossVia_homogeneous (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    (probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).IsHomogeneous
      (D.parity i * D.parity j) :=
  distinctTransport_homogeneous _ _ _
    (Superfunctor.mem_parity_iff_isHomogeneous.mp
      (Superfunctor.whiskerLeft_mem (probeOldBlockEval D Sc m Λ β)
        (probeOldBlockDistinctCross_mem D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε)))

/-- The supported component uses precisely the two selected product-coordinate equalities. -/
theorem probeOldWeightDistinctCrossVia_component (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (p : ZMod 2) (N : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app p N =
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) N) ≫
        (probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app p (N β) ≫
      eqToHom (Functor.congr_obj
        (probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε (sw hε)) N).symm :=
  distinctTransport_component _ _ _ p N

theorem probeOldWeightDistinctCrossVia_eq (β β' : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (hε' : blockSucc₂ D i j Λ h₁ h₂ β' = ε) :
    probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε =
      probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β' ε hε' := by
  obtain rfl := blockSucc₂_injective D i j Λ h₁ h₂ (hε.trans hε'.symm)
  rfl

/-- The actual weight-product crossing component, zero at absent predecessors. -/
def probeOldWeightDistinctCrossComponent (p : ZMod 2)
    (N : ProbeOldWeightProduct D Sc m Λ x₀) (ε : WeightBlocks D Λ xu) :
    (Fs ε).obj N ⟶ (Ft ε).obj N :=
  if hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε then
    (probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ hε.choose ε hε.choose_spec).app p N
  else 0

theorem probeOldWeightDistinctCrossComponent_of (p : ZMod 2)
    (N : ProbeOldWeightProduct D Sc m Λ x₀) (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ p N ε =
      (probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app p N := by
  unfold probeOldWeightDistinctCrossComponent
  split
  · rename_i hchoice
    rw [probeOldWeightDistinctCrossVia_eq D Sc m i j Λ h₁ h₂ h₃ h₄ hchoice.choose β ε hchoice.choose_spec hε]
  · rename_i hn
    exact absurd (⟨β, hε⟩ : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε) hn

theorem probeOldWeightDistinctCrossComponent_mem (p : ZMod 2)
    (N : ProbeOldWeightProduct D Sc m Λ x₀) (ε : WeightBlocks D Λ xu) :
    probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ p N ε ∈
      parity (R := k) _ _ p := by
  unfold probeOldWeightDistinctCrossComponent
  split
  · exact SuperNatTrans.app_mem _ p N
  · exact Submodule.zero_mem _

theorem probeOldWeightDistinctCrossComponent_naturality (p : ZMod 2) (ε : WeightBlocks D Λ xu)
    {N N' : ProbeOldWeightProduct D Sc m Λ x₀} {q : ZMod 2} (f : N ⟶ N')
    (hf : f ∈ parity (R := k) _ _ q) :
    (Fs ε).map f ≫ probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ p N' ε =
      koszulSign p q • (probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ p N ε ≫
        (Ft ε).map f) := by
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldWeightDistinctCrossComponent_of D Sc m i j Λ h₁ h₂ h₃ h₄ p N β ε hβ,
      probeOldWeightDistinctCrossComponent_of D Sc m i j Λ h₁ h₂ h₃ h₄ p N' β ε hβ]
    exact (probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hβ).naturality p f hf
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i j Λ h₁ h₂ ε hε N).eq_of_src _ _

/-- The positive distinct crossing on the whole original-weight product. -/
def probeOldWeightDistinctCross : SuperNatTrans k
    (probeOldEFunctor D Sc m j Λ h₁ ⋙ probeOldEFunctor D Sc m i Λ h₂)
    (probeOldEFunctor D Sc m i Λ h₃ ⋙ probeOldEFunctor D Sc m j Λ h₄) where
  app p N ε := probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ p N ε
  app_mem p N ε := probeOldWeightDistinctCrossComponent_mem D Sc m i j Λ h₁ h₂ h₃ h₄ p N ε
  naturality p _ _ _ f hf := funext fun ε =>
    probeOldWeightDistinctCrossComponent_naturality D Sc m i j Λ h₁ h₂ h₃ h₄ p ε f hf

theorem probeOldWeightDistinctCross_homogeneous :
    (probeOldWeightDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).IsHomogeneous
      (D.parity i * D.parity j) := by
  intro q hq
  funext N ε
  change probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ q N ε = 0
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldWeightDistinctCrossComponent_of D Sc m i j Λ h₁ h₂ h₃ h₄ q N β ε hβ]
    exact congrFun (probeOldWeightDistinctCrossVia_homogeneous D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hβ q hq) N
  · simp only [probeOldWeightDistinctCrossComponent, dite_eq_right hε]

/-- The prescribed crossing as a homogeneous two-morphism in the action target. -/
def probeOldActionDistinctCross :
    probeOldE D Sc m j Λ h₁ ≫ probeOldE D Sc m i Λ h₂ ⟶
      probeOldE D Sc m i Λ h₃ ≫ probeOldE D Sc m j Λ h₄ :=
  probeOldWeightDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄

theorem probeOldActionDistinctCross_mem :
    probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ ∈ parity (R := k) _ _
      (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (probeOldWeightDistinctCross_homogeneous D Sc m i j Λ h₁ h₂ h₃ h₄)
end Crossing
end OddMath.QuiverHecke
end

end

section

/-! # The selected right adjunction of the global OLD probe

`SwappedActionAssembly` F1: assemble the exact balanced old append
unit and counit over all original-weight content blocks, including absent
predecessors. Both triangles and evenness are proved for all evaluated
module inputs; no factor-action or local-inversion premise is supplied.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
open ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

abbrev probeOldBlockAdj (β : WeightBlocks D Λ x) :
    (probeOldBlockInd D Sc m i Λ h β).toFunctor ⊣
      (probeOldBlockRes D Sc m i Λ h β).toFunctor :=
  probeAppendToAdjunction D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _

/-- The unit component at a block of weight `x`. -/
def probeOldWeightUnitApp (β : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x) :
    M β ⟶ (probeOldBlockRes D Sc m i Λ h β).obj
      ((probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).obj M) :=
  (probeOldBlockAdj D Sc m i Λ h β).unit.app (M β) ≫
    (probeOldBlockRes D Sc m i Λ h β).map
      (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm)

theorem probeOldWeightUnitApp_naturality (β : WeightBlocks D Λ x)
    {M M' : ProbeOldWeightProduct D Sc m Λ x} (f : M ⟶ M') :
    f β ≫ probeOldWeightUnitApp D Sc m i Λ h β M' =
      probeOldWeightUnitApp D Sc m i Λ h β M ≫ (probeOldBlockRes D Sc m i Λ h β).map
        ((probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [probeOldInductionComponent_map_blockSucc]
  simp only [probeOldWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Functor.map_comp, ← Adjunction.unit_naturality_assoc]

/-- The unit on weight spaces. -/
def probeOldWeightUnit : 𝟭 (ProbeOldWeightProduct D Sc m Λ x) ⟶
    probeOldEFunctor D Sc m i Λ h ⋙ (probeOldF D Sc m i Λ h).toFunctor where
  app M β := probeOldWeightUnitApp D Sc m i Λ h β M
  naturality _ _ f := funext fun β => probeOldWeightUnitApp_naturality D Sc m i Λ h β f

/-- The counit at a block with a chosen predecessor. -/
def probeOldWeightCounitVia (N : ProbeOldWeightProduct D Sc m Λ y) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj ((probeOldF D Sc m i Λ h).obj N) ⟶ N δ := by
  subst hβ
  exact eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β _) ≫
    (probeOldBlockAdj D Sc m i Λ h β).counit.app (N (blockSucc D Λ i h β))

theorem probeOldWeightCounitVia_eq (N : ProbeOldWeightProduct D Sc m Λ y) (β β' : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) (hβ' : blockSucc D Λ i h β' = δ) :
    probeOldWeightCounitVia D Sc m i Λ h N β δ hβ =
      probeOldWeightCounitVia D Sc m i Λ h N β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The counit component at a block: through the predecessor, or zero. -/
def probeOldWeightCounitComponent (N : ProbeOldWeightProduct D Sc m Λ y) (δ : WeightBlocks D Λ y) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj ((probeOldF D Sc m i Λ h).obj N) ⟶ N δ :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    probeOldWeightCounitVia D Sc m i Λ h N hδ.choose δ hδ.choose_spec
  else 0

theorem probeOldWeightCounitComponent_blockSucc (N : ProbeOldWeightProduct D Sc m Λ y)
    (β : WeightBlocks D Λ x) :
    probeOldWeightCounitComponent D Sc m i Λ h N (blockSucc D Λ i h β) =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β
        ((probeOldF D Sc m i Λ h).obj N)) ≫
        (probeOldBlockAdj D Sc m i Λ h β).counit.app (N (blockSucc D Λ i h β)) := by
  unfold probeOldWeightCounitComponent
  split
  · rename_i hc
    exact probeOldWeightCounitVia_eq D Sc m i Λ h N _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem probeOldWeightCounitComponent_naturality (β : WeightBlocks D Λ x)
    {N N' : ProbeOldWeightProduct D Sc m Λ y} (g : N ⟶ N') :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map
        ((probeOldF D Sc m i Λ h).map g) ≫
      probeOldWeightCounitComponent D Sc m i Λ h N' (blockSucc D Λ i h β) =
    probeOldWeightCounitComponent D Sc m i Λ h N (blockSucc D Λ i h β) ≫
      g (blockSucc D Λ i h β) := by
  rw [probeOldInductionComponent_map_blockSucc, probeOldWeightCounitComponent_blockSucc,
    probeOldWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  exact (probeOldBlockAdj D Sc m i Λ h β).counit_naturality (g (blockSucc D Λ i h β))

/-- The counit on weight spaces. -/
def probeOldWeightCounit : (probeOldF D Sc m i Λ h).toFunctor ⋙ probeOldEFunctor D Sc m i Λ h ⟶
    𝟭 (ProbeOldWeightProduct D Sc m Λ y) where
  app N δ := probeOldWeightCounitComponent D Sc m i Λ h N δ
  naturality N N' g := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeightCounitComponent_naturality D Sc m i Λ h β g
    · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src _ _

theorem probeOldWeight_left_triangle (β : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map
        ((probeOldWeightUnit D Sc m i Λ h).app M) ≫
      probeOldWeightCounitComponent D Sc m i Λ h ((probeOldEFunctor D Sc m i Λ h).obj M)
        (blockSucc D Λ i h β) = 𝟙 _ := by
  rw [probeOldInductionComponent_map_blockSucc, probeOldWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  change eqToHom _ ≫ (probeOldBlockInd D Sc m i Λ h β).map (probeOldWeightUnitApp D Sc m i Λ h β M) ≫
    _ = _
  simp only [probeOldWeightUnitApp, Superfunctor.map, Functor.map_comp, Category.assoc]
  erw [Adjunction.counit_naturality, Adjunction.left_triangle_components_assoc]
  simp

theorem probeOldWeight_right_triangle (β : WeightBlocks D Λ x) (N : ProbeOldWeightProduct D Sc m Λ y) :
    probeOldWeightUnitApp D Sc m i Λ h β ((probeOldF D Sc m i Λ h).obj N) ≫
      (probeOldBlockRes D Sc m i Λ h β).map
        (probeOldWeightCounitComponent D Sc m i Λ h N (blockSucc D Λ i h β)) = 𝟙 _ := by
  rw [probeOldWeightCounitComponent_blockSucc]
  simp only [probeOldWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (probeOldBlockAdj D Sc m i Λ h β).right_triangle_components _

/-- **Induction is left adjoint to restriction on weight spaces.** -/
def probeOldWeightAdjunction :
    probeOldEFunctor D Sc m i Λ h ⊣ (probeOldF D Sc m i Λ h).toFunctor where
  unit := probeOldWeightUnit D Sc m i Λ h
  counit := probeOldWeightCounit D Sc m i Λ h
  left_triangle_components M := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeight_left_triangle D Sc m i Λ h β M
    · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src _ _
  right_triangle_components N := funext fun β => probeOldWeight_right_triangle D Sc m i Λ h β N

theorem probeOldBlockAdj_unit_mem (β : WeightBlocks D Λ x)
    (M : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockAdj D Sc m i Λ h β).unit.app M ∈ parity (R := k) _ _ 0 :=
  probeAppendToAdjunction_unit_mem D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _ M

theorem probeOldBlockAdj_counit_mem (β : WeightBlocks D Λ x)
    (M : ProbeCanonicalModules D Sc m (blockSucc D Λ i h β).1) :
    (probeOldBlockAdj D Sc m i Λ h β).counit.app M ∈ parity (R := k) _ _ 0 :=
  probeAppendToAdjunction_counit_mem D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _ M

theorem probeOldWeightUnitApp_mem (β : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x) :
    probeOldWeightUnitApp D Sc m i Λ h β M ∈ parity (R := k) _ _ 0 := by
  unfold probeOldWeightUnitApp
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (probeOldBlockAdj_unit_mem D Sc m i Λ h β (M β))
    (IsSuperfunctor.map_mem (F := (probeOldBlockRes D Sc m i Λ h β).toFunctor)
      (eqToHom_mem_parity_zero (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm))

theorem probeOldWeightUnit_mem (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldWeightUnit D Sc m i Λ h).app M ∈ parity (R := k) _ _ 0 := fun β =>
  probeOldWeightUnitApp_mem D Sc m i Λ h β M

theorem probeOldWeightCounit_mem (M : ProbeOldWeightProduct D Sc m Λ y) :
    (probeOldWeightCounit D Sc m i Λ h).app M ∈ parity (R := k) _ _ 0 := fun δ => by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change probeOldWeightCounitComponent D Sc m i Λ h M (blockSucc D Λ i h β) ∈ _
    rw [probeOldWeightCounitComponent_blockSucc, ← zero_add (0 : ZMod 2)]
    exact comp_mem (eqToHom_mem_parity_zero (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β
        ((probeOldF D Sc m i Λ h).obj M)))
      (probeOldBlockAdj_counit_mem D Sc m i Λ h β (M (blockSucc D Λ i h β)))
  · rw [(probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src
      ((probeOldWeightCounit D Sc m i Λ h).app M δ) 0]
    exact Submodule.zero_mem _

/-- The actual OLD probe weight functors carry the prescribed even right adjunction. -/
def probeOldActionAdjunction :
    SKM.SuperAdjunction (k := k) (probeOldE D Sc m i Λ h) (probeOldF D Sc m i Λ h) :=
  ELV.ordinaryEvenSuperAdjunction (probeOldE D Sc m i Λ h) (probeOldF D Sc m i Λ h)
    (probeOldWeightAdjunction D Sc m i Λ h) (probeOldWeightUnit_mem D Sc m i Λ h)
    (probeOldWeightCounit_mem D Sc m i Λ h)

end OddMath.QuiverHecke
end

end

section

/-! # Whole signed dot unit with stored OLD probe contents

SwappedActionAssembly F2: every prescribed retargeted append induction
has its natural signed-dot inverse on all scalar-evaluated OLD modules.
Only the content certificate changes; the old coend and physical arrow
are retained. No component invertibility premise is supplied.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
private theorem appendTo_transform_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ J.obj v} (hα : IsSupernatural k p α)
    (N : Superfunctor k C (SVec k)) (t : A) :
    (transformComponent hα N).total t = transformLinear hα N t := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ)
local notation "J" => oldContentAppendTo D Sc (probeCutoff D m) ν i μ h
/-- The unchanged physical quotient dot at the specified target content. -/
def probeAppendToDot (v : OldContentCategory D Sc (probeCutoff D m) ν) :
    (J).obj v ⟶ (J).obj v :=
  CyclotomicCrossingTensor.oldAppendDotComponent D Sc (probeCutoff D m) i v.obj

theorem probeAppendToDot_supernatural : IsSupernatural k (D.parity i) (probeAppendToDot D Sc m ν i μ h) where
  mem v := (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc (probeCutoff D m) i).mem v.obj
  naturality hf := (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc (probeCutoff D m) i).naturality hf
local notation "hDot" => probeAppendToDot_supernatural D Sc m ν i μ h
local notation "E" => probeEvaluatedAppendTo D Sc m ν i μ h

/-- The chosen signed dot, retaining its whole module morphism. -/
def probeAppendToDotComponent (N : ProbeEvaluatedModules D Sc m ν) :
    (E).obj N ⟶ (E).obj N := ⟨transformComponent hDot N.obj⟩

theorem probeAppendToDotComponent_supernatural :
    IsSupernatural k (D.parity i) (F := E) (G := E)
      (probeAppendToDotComponent D Sc m ν i μ h) where
  mem N := transformComponent_mem hDot N.obj
  naturality := by
    intro M N p f hf
    apply InducedCategory.hom_ext
    change f.hom ∈ parity (R := k) _ _ p at hf
    exact (transformComponent_supernatural hDot).naturality hf

/-- The whole signed dot on the actual evaluated induction functor. -/
def probeAppendToInductionDot :
    End (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m μ)) :=
  (probeAppendToDotComponent_supernatural D Sc m ν i μ h).toSuperNatTrans

theorem probeAppendToInductionDot_mem :
    probeAppendToInductionDot D Sc m ν i μ h ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem
    (probeAppendToDotComponent_supernatural D Sc m ν i μ h)

/-- The whole functor dot has exactly the prescribed native module component. -/
theorem probeAppendToInductionDot_total (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToInductionDot D Sc m ν i μ h).total N = probeAppendToDotComponent D Sc m ν i μ h N :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m μ)))
    (G := (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m μ)))
    (probeAppendToDotComponent_supernatural D Sc m ν i μ h) N

private theorem appendTo_dot_eq (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (t : OldContentCategory D Sc (probeCutoff D m) μ) :
    transformLinear hDot N t = probeOldContentInductionDot D Sc m ν i N
      ((oldContentReindex D Sc (probeCutoff D m) h.symm).obj t) := rfl

variable [Fintype I]

/-- Every evaluated old probe module has the prescribed dot isomorphism;
the inverse comes from the actual scalar quotient, with no inverse premise. -/
def probeAppendToDotModuleIso [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    induced J N.obj ≅ induced J N.obj :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals
    (transformComponent hDot N.obj) (transformComponent_mem hDot N.obj) (by
      intro t
      rw [appendTo_transform_total]
      rw [appendTo_dot_eq]
      have h := probeOldContentInductionDot_isUnit D Sc m ν i N.obj N.property
        ((oldContentReindex D Sc (probeCutoff D m) h.symm).obj t)
      exact (Module.End.isUnit_iff _).mp h)

/-- The dot isomorphism retains the exact specified module forward. -/
theorem probeAppendToDotModuleIso_hom [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToDotModuleIso D Sc m ν i μ h N).hom = transformComponent hDot N.obj :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals_hom _ _ _

/-- The pointwise inverse is a morphism of the same full evaluated category. -/
def probeAppendToDotIso [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) : (E).obj N ≅ (E).obj N :=
  ObjectProperty.isoMk (ProbeEvaluatesCoefficients D m Sc μ) (probeAppendToDotModuleIso D Sc m ν i μ h N)

private theorem appendToDotIso_hom_total [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToDotIso D Sc m ν i μ h N).hom = (probeAppendToInductionDot D Sc m ν i μ h).total N := by
  rw [probeAppendToInductionDot_total]
  apply InducedCategory.hom_ext
  exact probeAppendToDotModuleIso_hom D Sc m ν i μ h N

/-- The actual dot inverse is natural on the entire evaluated probe category. -/
def probeAppendToInductionDotIso [Fact Sc.PureNilpotent] :
    (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m μ)) ≅ ⟨E⟩ :=
  OddMath.HomogeneousSuperfunctorIso.ofHom
    (probeAppendToInductionDot D Sc m ν i μ h) (probeAppendToInductionDot_mem D Sc m ν i μ h)
    (probeAppendToDotIso D Sc m ν i μ h) (appendToDotIso_hom_total D Sc m ν i μ h)

@[simp] theorem probeAppendToInductionDotIso_hom [Fact Sc.PureNilpotent] :
    (probeAppendToInductionDotIso D Sc m ν i μ h).hom = probeAppendToInductionDot D Sc m ν i μ h :=
  OddMath.HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

/-- Whole-functor invertibility is proved, rather than assumed componentwise. -/
theorem probeAppendToInductionDot_isUnit [Fact Sc.PureNilpotent] : IsUnit (End.of (probeAppendToInductionDot D Sc m ν i μ h)) := by
  apply (isUnit_iff_isIso _).2
  rw [← probeAppendToInductionDotIso_hom]
  infer_instance

end OddMath.QuiverHecke
end

end

section

/-! # The prescribed signed dot on the global OLD probe

`SwappedActionAssembly` F2: the actual old append dot acts on every
original-weight block. Its only nonzero parity component is the moving
colour parity. Absent predecessors contribute the zero module. No
invertibility statement is made for arbitrary unevaluated old modules.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
open ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The exact chosen stored-target OLD dot, without a comparison isomorphism. -/
abbrev probeOldBlockDot (β : WeightBlocks D Λ x) :=
  probeAppendToInductionDot D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList
    (by
      apply Multiset.coe_eq_coe.mp
      rw [Multiset.coe_toList]
      change {i} + (β.1.toList : Multiset I) = (blockSucc D Λ i h β).1
      rw [Multiset.coe_toList, blockSucc_val])

theorem probeOldBlockDot_mem (β : WeightBlocks D Λ x) :
    probeOldBlockDot D Sc m i Λ h β ∈ parity (R := k)
      (probeOldBlockInd D Sc m i Λ h β) (probeOldBlockInd D Sc m i Λ h β) (D.parity i) :=
  probeAppendToInductionDot_mem D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _

theorem probeOldBlockDot_homogeneous (β : WeightBlocks D Λ x) :
    (probeOldBlockDot D Sc m i Λ h β).IsHomogeneous (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.1 (probeOldBlockDot_mem D Sc m i Λ h β)

/-- The dot component at a block with a chosen predecessor. -/
def probeOldWeightDotVia (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj M ⟶ (probeOldInductionComponent D Sc m i Λ h δ).obj M := by
  subst hβ
  exact eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) ≫
    (probeOldBlockDot D Sc m i Λ h β).app p (M β) ≫
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm

theorem probeOldWeightDotVia_eq (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (β β' : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    probeOldWeightDotVia D Sc m i Λ h p M β δ hβ =
      probeOldWeightDotVia D Sc m i Λ h p M β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The dot component at a block: through the predecessor, or zero. -/
def probeOldWeightDotComponent (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (δ : WeightBlocks D Λ y) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj M ⟶ (probeOldInductionComponent D Sc m i Λ h δ).obj M :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    probeOldWeightDotVia D Sc m i Λ h p M hδ.choose δ hδ.choose_spec
  else 0

theorem probeOldWeightDotComponent_blockSucc (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (β : WeightBlocks D Λ x) :
    probeOldWeightDotComponent D Sc m i Λ h p M (blockSucc D Λ i h β) =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) ≫
        (probeOldBlockDot D Sc m i Λ h β).app p (M β) ≫
          eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm := by
  unfold probeOldWeightDotComponent
  split
  · rename_i hc
    exact probeOldWeightDotVia_eq D Sc m i Λ h p M _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem probeOldWeightDotComponent_mem (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (δ : WeightBlocks D Λ y) :
    probeOldWeightDotComponent D Sc m i Λ h p M δ ∈ parity (R := k) _ _ p := by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [probeOldWeightDotComponent_blockSucc]
    have hm := comp_mem (eqToHom_mem_parity_zero
        (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M))
      (comp_mem ((probeOldBlockDot D Sc m i Λ h β).app_mem p (M β))
        (eqToHom_mem_parity_zero (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm))
    simpa only [zero_add, add_zero] using hm
  · rw [(probeOldInductionComponent_isZero D Sc m i Λ h δ hδ M).eq_of_src
      (probeOldWeightDotComponent D Sc m i Λ h p M δ) 0]
    exact Submodule.zero_mem _

theorem probeOldWeightDotComponent_naturality (p : ZMod 2) (β : WeightBlocks D Λ x)
    {M M' : ProbeOldWeightProduct D Sc m Λ x} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f ≫
        probeOldWeightDotComponent D Sc m i Λ h p M' (blockSucc D Λ i h β) =
      koszulSign p q • (probeOldWeightDotComponent D Sc m i Λ h p M (blockSucc D Λ i h β) ≫
        (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [probeOldInductionComponent_map_blockSucc, probeOldWeightDotComponent_blockSucc,
    probeOldWeightDotComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hn := (probeOldBlockDot D Sc m i Λ h β).naturality p (f β) (hf β)
  rw [← Category.assoc ((probeOldBlockInd D Sc m i Λ h β).map (f β)), Superfunctor.map, hn,
    Linear.smul_comp, Linear.comp_smul, Category.assoc]

/-- **The dot on weight-space induction.** -/
def probeOldWeightDot :
    SuperNatTrans k (probeOldEFunctor D Sc m i Λ h) (probeOldEFunctor D Sc m i Λ h) where
  app p M δ := probeOldWeightDotComponent D Sc m i Λ h p M δ
  app_mem p M δ := probeOldWeightDotComponent_mem D Sc m i Λ h p M δ
  naturality p M M' q f hf := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeightDotComponent_naturality D Sc m i Λ h p β f hf
    · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src _ _

/-- Only the component of the colour parity is nonzero. -/
theorem probeOldWeightDot_homogeneous :
    (probeOldWeightDot D Sc m i Λ h).IsHomogeneous (D.parity i) := by
  intro q hq
  funext M
  funext δ
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change probeOldWeightDotComponent D Sc m i Λ h q M (blockSucc D Λ i h β) = 0
    rw [probeOldWeightDotComponent_blockSucc,
      congrFun (probeOldBlockDot_homogeneous D Sc m i Λ h β q hq)
        (M β)]
    simp
  · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ M).eq_of_src _ _

/-- The dot as a 2-endomorphism of weight-space induction in the action target. -/
def probeOldActionDot : probeOldE D Sc m i Λ h ⟶ probeOldE D Sc m i Λ h :=
  probeOldWeightDot D Sc m i Λ h

/-- The dot has the parity of its colour, including for odd colours. -/
theorem probeOldActionDot_mem :
    probeOldActionDot D Sc m i Λ h ∈
      parity (R := k) (probeOldE D Sc m i Λ h) (probeOldE D Sc m i Λ h)
        (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.2 (probeOldWeightDot_homogeneous D Sc m i Λ h)

end OddMath.QuiverHecke
end

end

section

/-! # Whole dot units on every original-weight OLD probe category

SwappedActionAssembly F2: the chosen signed dot is a unit of the entire
weight-induction endomorphism ring. The actual scalar-quotient inverse
works at every predecessor; absent predecessors have the zero module.
The original weight fibre may be infinite, with no uniform exponent.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV CyclotomicAction SwappedAssembly
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
theorem probeOldBlockDot_isUnit [Fact Sc.PureNilpotent] (β : WeightBlocks D Λ x) :
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
theorem probeOldActionDot_component_isUnit [Fact Sc.PureNilpotent] (M : ProbeOldWeightProduct D Sc m Λ x)
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
def probeOldActionDotIso [Fact Sc.PureNilpotent] : probeOldE D Sc m i Λ h ≅ probeOldE D Sc m i Λ h :=
  homogeneousTotalUnitIso (probeOldE D Sc m i Λ h) (probeOldActionDot D Sc m i Λ h)
    (probeOldActionDot_mem D Sc m i Λ h) (fun M =>
      productEnd_isUnit (fun δ : WeightBlocks D Λ y => ProbeCanonicalModules D Sc m δ.1)
        ((probeOldE D Sc m i Λ h).obj M) ((probeOldActionDot D Sc m i Λ h).total M)
        (probeOldActionDot_component_isUnit D Sc m i Λ h M))

@[simp] theorem probeOldActionDotIso_hom [Fact Sc.PureNilpotent] :
    (probeOldActionDotIso D Sc m i Λ h).hom = probeOldActionDot D Sc m i Λ h :=
  homogeneousTotalUnitIso_hom _ _ _ _

/-- Whole natural invertibility of the prescribed signed probe dot. -/
theorem probeOldActionDot_isUnit [Fact Sc.PureNilpotent] : IsUnit (End.of (probeOldActionDot D Sc m i Λ h)) := by
  apply (isUnit_iff_isIso _).mpr
  rw [← probeOldActionDotIso_hom]
  infer_instance

end OddMath.QuiverHecke
end

end

section

/-! # OLD probe Rouquier generator data

Brundan–Ellis Definition 1.5 and (1.8)–(1.9): assemble the chosen probe
weight spaces, induction and signed dots with the negative equal crossing
and positive distinct crossing. Restriction and its prescribed adjunction,
the equal square and braid, and the natural dot unit are retained. Local
inversion records and multicolour coherence remain separate obligations.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u
private theorem braid_of_equal_crosses
    {k : Type u} [CommRing k] {A B C E : PiSCat.{u,u,u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ E)
    (t₁ u₁ : End (F ≫ G)) (t₂ u₂ : End (G ≫ H))
    (e₁ : u₁ = t₁) (e₂ : u₂ = t₂)
    (hb : let p := (associator F G H).inv ≫ t₁ ▷ H ≫ (associator F G H).hom
      let s := F ◁ t₂
      s ≫ p ≫ s = p ≫ s ≫ p) :
    let p := (associator F G H).inv ≫ u₁ ▷ H ≫ (associator F G H).hom
    let s := F ◁ u₂
    s ≫ p ≫ s = p ≫ s ≫ p := by
  cases e₁
  cases e₂
  exact hb

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (Λ : X)

/-- The selected crossing, using the negative equal and positive distinct maps. -/
def probeOldActionCross (i j : I) {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d) :
    probeOldE D Sc m j Λ h₁ ≫ probeOldE D Sc m i Λ h₂ ⟶
      probeOldE D Sc m i Λ h₃ ≫ probeOldE D Sc m j Λ h₄ :=
  if hij : i = j then by
    subst j
    have hbc : b = c := h₁.symm.trans h₃
    cases hbc
    exact probeOldActionEqualCross D Sc m i Λ h₁ h₂
  else probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄

theorem probeOldActionCross_equal (i : I) {a b c : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) :
    probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂ =
      probeOldActionEqualCross D Sc m i Λ h₁ h₂ := by
  rw [probeOldActionCross, dite_eq_left rfl]

theorem probeOldActionCross_distinct (i j : I) (hij : i ≠ j) {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d) :
    probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄ =
      probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ := by
  simp only [probeOldActionCross, dite_eq_right hij]

theorem probeOldActionCross_mem (i j : I) {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d) :
    probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄ ∈ parity (R := k) _ _
      (D.parity i * D.parity j) := by
  by_cases hij : i = j
  · subst j
    have hbc : b = c := h₁.symm.trans h₃
    cases hbc
    rw [probeOldActionCross_equal, SKM.zmod2_mul_self]
    exact probeOldActionEqualCross_mem D Sc m i Λ h₁ h₂
  · rw [probeOldActionCross_distinct D Sc m Λ i j hij]
    exact probeOldActionDistinctCross_mem D Sc m i j Λ h₁ h₂ h₃ h₄

/-- The selected generators, without assuming any local inverse record. -/
def probeOldRouquierData :
    SKM.RouquierData (k := k) (B := PiSCat.{u,u,u + 1} k) D where
  obj x := probeOldWeightSpace D Sc m Λ x
  E i _ _ h := probeOldE D Sc m i Λ h
  dot i _ _ h := probeOldActionDot D Sc m i Λ h
  dot_mem i _ _ h := probeOldActionDot_mem D Sc m i Λ h
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ := probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄
  cross_mem i j _ _ _ _ h₁ h₂ h₃ h₄ := probeOldActionCross_mem D Sc m Λ i j h₁ h₂ h₃ h₄

/-- The right adjunction uses the selected restriction and unchanged unit and counit. -/
def probeOldRouquierDataAdjunction (i : I) {x y : X} (h : x + D.α i = y) :
    SKM.SuperAdjunction (k := k) ((probeOldRouquierData D Sc m Λ).E i h)
      (probeOldF D Sc m i Λ h) :=
  probeOldActionAdjunction D Sc m i Λ h

theorem probeOldRouquierData_dot_isUnit [Fact Sc.PureNilpotent] [Fintype I] (i : I) {x y : X} (h : x + D.α i = y) :
    IsUnit (End.of ((probeOldRouquierData D Sc m Λ).dot i h)) :=
  probeOldActionDot_isUnit D Sc m i Λ h

theorem probeOldRouquierData_square (i : I) {a b c : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) :
    (probeOldRouquierData D Sc m Λ).cross i i h₁ h₂ h₁ h₂ ≫
      (probeOldRouquierData D Sc m Λ).cross i i h₁ h₂ h₁ h₂ = 0 := by
  change probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂ ≫
    probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂ = 0
  rw [probeOldActionCross_equal]
  exact probeOldActionEqualCross_square D Sc m i Λ h₁ h₂

theorem probeOldRouquierData_braid (i : I) {a b c d : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) (h₃ : c + D.α i = d) :
    let E₁ := (probeOldRouquierData D Sc m Λ).E i h₁
    let E₂ := (probeOldRouquierData D Sc m Λ).E i h₂
    let E₃ := (probeOldRouquierData D Sc m Λ).E i h₃
    let t₁ := (associator E₁ E₂ E₃).inv ≫
      (probeOldRouquierData D Sc m Λ).cross i i h₁ h₂ h₁ h₂ ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom
    let t₂ := E₁ ◁ (probeOldRouquierData D Sc m Λ).cross i i h₂ h₃ h₂ h₃
    t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁ := by
  exact braid_of_equal_crosses
    (probeOldE D Sc m i Λ h₁) (probeOldE D Sc m i Λ h₂) (probeOldE D Sc m i Λ h₃)
    (probeOldActionEqualCross D Sc m i Λ h₁ h₂)
    (probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂)
    (probeOldActionEqualCross D Sc m i Λ h₂ h₃)
    (probeOldActionCross D Sc m Λ i i h₂ h₃ h₂ h₃)
    (probeOldActionCross_equal D Sc m Λ i h₁ h₂)
    (probeOldActionCross_equal D Sc m Λ i h₂ h₃)
    (probeOldActionEqualCross_braid D Sc m i Λ h₁ h₂ h₃)

end OddMath.QuiverHecke
end

end
