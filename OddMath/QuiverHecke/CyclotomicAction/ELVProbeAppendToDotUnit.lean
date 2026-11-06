/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCanonicalContent
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDotUnit

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
open ELVOld ELVOld.BalancedInduction
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
