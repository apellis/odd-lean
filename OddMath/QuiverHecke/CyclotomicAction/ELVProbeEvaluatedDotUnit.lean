/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedCategory

/-! # Whole signed dot unit on the evaluated old probe category

`SwappedNondegeneracy` §3 and `SwappedActionAssembly` F2 require a natural
probe-dot inverse on the actual factor category. The full scalar-evaluated
old module subcategory supplies the actual algebra-quotient inverse for
every object. Pointwise homogeneous inverses assemble into an isomorphism
of the prescribed induction superfunctor, including odd colour parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
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

/-- Every evaluated old probe module has the prescribed dot isomorphism;
the inverse comes from the actual scalar quotient, with no inverse premise. -/
def probeEvaluatedDotModuleIso (N : ProbeEvaluatedModules D Sc m ν) :
    induced J N.obj ≅ induced J N.obj :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals
    (transformComponent hDot N.obj) (transformComponent_mem hDot N.obj) (by
      intro t
      rw [transform_total]
      change Function.Bijective (probeOldContentInductionDot D Sc m ν i N.obj t)
      have h := probeOldContentInductionDot_isUnit D Sc m ν i N.obj N.property t
      exact (Module.End.isUnit_iff _).mp h)

/-- The dot isomorphism retains the exact specified module forward. -/
theorem probeEvaluatedDotModuleIso_hom (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedDotModuleIso D Sc m ν i N).hom = transformComponent hDot N.obj :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals_hom _ _ _

/-- The pointwise inverse is a morphism of the same full evaluated category. -/
def probeEvaluatedDotIso (N : ProbeEvaluatedModules D Sc m ν) : (E).obj N ≅ (E).obj N :=
  ObjectProperty.isoMk (ProbeEvaluatesCoefficients D m Sc (i :: ν)) (probeEvaluatedDotModuleIso D Sc m ν i N)

private theorem evaluatedDotIso_hom_total (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedDotIso D Sc m ν i N).hom = (probeEvaluatedInductionDot D Sc m ν i).total N := by
  rw [probeEvaluatedInductionDot_total]
  apply InducedCategory.hom_ext
  exact probeEvaluatedDotModuleIso_hom D Sc m ν i N

/-- The actual dot inverse is natural on the entire evaluated probe category. -/
def probeEvaluatedInductionDotIso :
    (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: ν))) ≅ ⟨E⟩ :=
  OddMath.HomogeneousSuperfunctorIso.ofHom
    (probeEvaluatedInductionDot D Sc m ν i) (probeEvaluatedInductionDot_mem D Sc m ν i)
    (probeEvaluatedDotIso D Sc m ν i) (evaluatedDotIso_hom_total D Sc m ν i)

@[simp] theorem probeEvaluatedInductionDotIso_hom :
    (probeEvaluatedInductionDotIso D Sc m ν i).hom = probeEvaluatedInductionDot D Sc m ν i :=
  OddMath.HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

variable [Fintype I]

end OddMath.QuiverHecke
