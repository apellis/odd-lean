import OddMath.QuiverHecke.CyclotomicAction.ELVProbeScalarModules

/-! # Literal ordinary Hom descent for scalar-evaluated old modules
The image of the original full old ideal is exactly the existing ordinary
cycHom ideal. Actual scalar-evaluated old modules therefore act on that
ordinary Hom quotient, using the proved representation factorization.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

/-- The scalar image of the full old ideal is the entire ordinary Hom ideal. -/
theorem elvProbeScalarHom_ideal_image (v w : List I) :
    (ELVOld.ideal D Sc cut v w).map (elvProbeScalarHom D m Sc v w) = cycHom D Sc a v w := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    exact elvProbeAffineSpecialization_ideal D m Sc hg
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,t,p,q,rfl⟩
    have hunit {s u : List I}
        (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D u)) :
        elvProbeScalarHom D m Sc s u (ELVOld.affineUnit D Sc cut s u f) = f := by
      change elvProbeScalarHom D m Sc s u ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cut) ⊗ₜ[k] f) = _
      rw [elvProbeScalarHom_tmul, map_one, one_smul]
    refine ⟨ELVOld.affineUnit D Sc cut _ _ p ≫ ELVOld.relation D Sc cut i t ≫
      ELVOld.affineUnit D Sc cut _ _ q, ?_, ?_⟩
    · exact Submodule.subset_span ⟨i,t,
        ELVOld.affineUnit D Sc cut _ _ p, ELVOld.affineUnit D Sc cut _ _ q,rfl⟩
    · rw [elvProbeScalarHom_comp, elvProbeScalarHom_comp,
        hunit, hunit, elvProbeScalarHom_relation]

variable (ν : List I)
local notation "C" => ELVOld.OldContentCategory D Sc cut ν
variable
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))

/-- No ordinary first-dot relation survives in an actual scalar-evaluated old module. -/
theorem probeOldModuleRawAction_kills_cycHom
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) (v w : C) :
    cycHom D Sc a v.obj.word w.obj.word ≤
      LinearMap.ker ((probeOldModuleRawAction D m Sc ν N v w).comp
        (ELVOld.affineUnit D Sc cut v.obj.word w.obj.word)) := by
  intro f hf
  rw [← elvProbeScalarHom_ideal_image D m Sc] at hf
  obtain ⟨g,hg,rfl⟩ := hf
  change probeOldModuleRawAction D m Sc ν N v w
    (ELVOld.affineUnit D Sc cut _ _ (elvProbeScalarHom D m Sc _ _ g)) = 0
  rw [← probeOldModuleRawAction_factor D m Sc ν N hN]
  have hz : (ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ g = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hg
  rw [probeOldModuleRawAction_apply, hz, N.toFunctor.map_zero]

/-- The literal ordinary cycHom quotient acts on the actual old module values. -/
def probeOrdinaryModuleHom (hN : ProbeEvaluatesCoefficients D m Sc ν N) (v w : C) :
    (((pres D Sc).obj (ob D v.obj.word) ⟶ (pres D Sc).obj (ob D w.obj.word)) ⧸
      cycHom D Sc a v.obj.word w.obj.word) →ₗ[k] (N.obj v ⟶ N.obj w) :=
  (cycHom D Sc a v.obj.word w.obj.word).liftQ
    ((probeOldModuleRawAction D m Sc ν N v w).comp
      (ELVOld.affineUnit D Sc cut v.obj.word w.obj.word))
    (probeOldModuleRawAction_kills_cycHom D m Sc ν N hN v w)

@[simp] theorem probeOrdinaryModuleHom_mk (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (v w : C) (f : (pres D Sc).obj (ob D v.obj.word) ⟶ (pres D Sc).obj (ob D w.obj.word)) :
    probeOrdinaryModuleHom D m Sc ν N hN v w ((cycHom D Sc a v.obj.word w.obj.word).mkQ f) =
      probeOldModuleRawAction D m Sc ν N v w (ELVOld.affineUnit D Sc cut v.obj.word w.obj.word f) := rfl

/-- This is descent of the existing actual old arrow action, not a new representation choice. -/
theorem probeOrdinaryModuleHom_old (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (v w : C) (f : v ⟶ w) :
    probeOrdinaryModuleHom D m Sc ν N hN v w
      (elvProbeOldHom D m Sc v.obj.word w.obj.word f) = N.toFunctor.map f := by
  obtain ⟨f,rfl⟩ := (ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ_surjective f
  rw [elvProbeOldHom_mk, probeOrdinaryModuleHom_mk]
  change probeOldModuleRawAction D m Sc ν N v w
    (ELVOld.affineUnit D Sc cut v.obj.word w.obj.word
      (elvProbeScalarHom D m Sc v.obj.word w.obj.word f)) =
        probeOldModuleRawAction D m Sc ν N v w f
  exact (probeOldModuleRawAction_factor D m Sc ν N hN v w f).symm

end OddMath.QuiverHecke

