import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryAppend
import StringDiagrams.Super.SVecQuotient

/-! # Super grading of the literal ordinary probe quotient category
Parity descends from the actual old ideal through the even scalar
specialization. This upgrades the checked full scalar, append and module
functors without a new homogeneous-generator hypothesis.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

theorem elvProbeScalarHom_proj {v w : List I} (p : ZMod 2)
    (f : ELVOld.hom D Sc cut v w) :
    elvProbeScalarHom D m Sc v w (proj k p f) =
      proj k p (elvProbeScalarHom D m Sc v w f) :=
  Supercategory.map_proj (elvProbeAffineSpecialization D m Sc).toFunctor p f

/-- The ordinary relation ideal inherits parity projection stability from the old ideal. -/
theorem probeCycHom_proj_mem {v w : List I}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ cycHom D Sc a v w) (p : ZMod 2) :
    proj k p f ∈ cycHom D Sc a v w := by
  rw [← elvProbeScalarHom_ideal_image D m Sc] at hf
  obtain ⟨g,hg,rfl⟩ := hf
  have h := elvProbeAffineSpecialization_ideal D m Sc (ELVOld.ideal_proj_mem D Sc cut hg p)
  rw [elvProbeScalarHom_proj] at h
  exact h

private def probeOrdinaryGradedIdeal (v w : List I) :
    SVec.GradedSubmodule (homSVec k (H D Sc) ((pres D Sc).obj (ob D v)) ((pres D Sc).obj (ob D w))) where
  toSubmodule := cycHom D Sc a v w
  odd_mem _f hf := probeCycHom_proj_mem D Sc m hf 1

/-- The literal ordinary Hom quotient with its inherited superspace structure. -/
def probeOrdinaryHomSpace (v w : List I) : SVec k :=
  SVec.quot (homSVec k (H D Sc) ((pres D Sc).obj (ob D v)) ((pres D Sc).obj (ob D w)))
    (probeOrdinaryGradedIdeal D Sc m v w)

theorem probeOrdinaryHomSpace_mk_mem {v w : List I} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ parity (R := k) _ _ p) :
    (cycHom D Sc a v w).mkQ f ∈ (probeOrdinaryHomSpace D Sc m v w).part p :=
  SVec.quotMkFun_mem_part _ _ ((mem_homSVec_part_iff k).mpr hf)

theorem probeOrdinaryHomSpace_lift {v w : List I} {p : ZMod 2}
    {f : (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a v w)}
    (hf : f ∈ (probeOrdinaryHomSpace D Sc m v w).part p) :
    ∃ g : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w),
      g ∈ parity (R := k) _ _ p ∧ (cycHom D Sc a v w).mkQ g = f := by
  obtain ⟨g,rfl⟩ := (cycHom D Sc a v w).mkQ_surjective f
  refine ⟨proj k p g, proj_mem p g, ?_⟩
  have h := (SVec.mem_part_iff _).mp hf
  change (SVec.quot _ (probeOrdinaryGradedIdeal D Sc m v w)).proj p
    (SVec.quotMkFun _ (probeOrdinaryGradedIdeal D Sc m v w) g) = _ at h
  rw [SVec.quot_proj_mk, homSVec_proj] at h
  exact h

instance probeOrdinarySupercategory (ν : List I) :
    Supercategory k (OrdinaryContentCategory D Sc a ν) where
  parity v w := (probeOrdinaryHomSpace D Sc m v.word w.word).part
  isInternal v w := SVec.isInternal_part _
  id_mem v := probeOrdinaryHomSpace_mk_mem D Sc m (id_mem _)
  comp_mem := by
    intro v t w p q f g hf hg
    obtain ⟨fr,hfr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hf
    obtain ⟨gr,hgr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hg
    exact probeOrdinaryHomSpace_mk_mem D Sc m (Supercategory.comp_mem hfr hgr)

instance probeOldOrdinaryFunctor_super (ν : List I) :
    IsSuperfunctor k (probeOldOrdinaryFunctor D Sc m ν) where
  map_mem := by
    intro v w p f hf
    obtain ⟨fr,hfr,rfl⟩ := hf
    apply probeOrdinaryHomSpace_mk_mem D Sc m
    exact (elvProbeAffineSpecialization D m Sc).map_mem hfr

instance probeOrdinaryAppend_super (ν : List I) (i : I) :
    IsSuperfunctor k (probeOrdinaryAppend D Sc m ν i) where
  map_mem := by
    intro v w p f hf
    obtain ⟨fr,hfr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hf
    exact probeOrdinaryHomSpace_mk_mem D Sc m
      (MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D [i])) hfr)

def probeOldOrdinarySuperfunctor (ν : List I) :
    Superfunctor k (ELVOld.OldContentCategory D Sc cut ν) (OrdinaryContentCategory D Sc a ν) :=
  ⟨probeOldOrdinaryFunctor D Sc m ν⟩

variable (ν : List I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

instance probeOrdinaryModuleFunctor_super :
    IsSuperfunctor k (probeOrdinaryModuleFunctor D Sc m ν N hN) where
  map_mem := by
    intro v w p f hf
    obtain ⟨fr,hfr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hf
    apply N.map_mem
    exact Submodule.mem_map_of_mem (ELVPScalar.affineUnit_mem D Sc cut hfr)

def probeOrdinaryModuleSuperfunctor :
    Superfunctor k (OrdinaryContentCategory D Sc a ν) (SVec k) :=
  ⟨probeOrdinaryModuleFunctor D Sc m ν N hN⟩

theorem probeOrdinaryModuleSuperfunctor_restrict :
    (probeOldOrdinarySuperfunctor D Sc m ν).comp
      (probeOrdinaryModuleSuperfunctor D Sc m ν N hN) = N := by
  apply Superfunctor.ext
  exact probeOrdinaryModuleFunctor_restrict D Sc m ν N hN

end OddMath.QuiverHecke

