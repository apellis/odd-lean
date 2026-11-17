import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Quotient.Bilinear
import StringDiagrams.Super.SVecQuotient
import OddMath.QuiverHecke.CyclotomicAction.ProbeScalarModules.ProbeDotPropagation

/-!
# Probe scalar modules

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The literal ordinary probe content category
Homs are the existing ordinary cycHom quotients. Canonical scalar
specialization is full, and actual scalar-evaluated old modules descend
through it with their original arrow action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (a : I → Polynomial k)

/-- Fixed-content words with the existing ordinary cyclotomic Hom quotients. -/
structure OrdinaryContentCategory (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (a : I → Polynomial k) (ν : List I) where
  word : List I
  wordPerm : word.Perm ν

def ordinaryContentComp (v t w : List I) :
    (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t)) ⧸ cycHom D Sc a v t) →ₗ[k]
    (((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a t w) →ₗ[k]
    (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a v w) :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun f =>
        { toFun := fun g => (cycHom D Sc a v w).mkQ (f ≫ g)
          map_add' := by intros; simp only [Preadditive.comp_add, map_add]
          map_smul' := by intros; simp only [Linear.comp_smul, map_smul, RingHom.id_apply] }
       map_add' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk,
         Preadditive.add_comp, map_add, LinearMap.add_apply]
       map_smul' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk,
         Linear.smul_comp, map_smul, LinearMap.smul_apply, RingHom.id_apply] } :
      ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t)) →ₗ[k]
      ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D w)) →ₗ[k] _)
    (by
      intro f hf
      ext g
      exact (Submodule.Quotient.mk_eq_zero _).mpr (cycHom_comp_right D Sc hf g))
    (by
      intro g hg
      ext f
      exact (Submodule.Quotient.mk_eq_zero _).mpr (cycHom_comp_left D Sc f hg))

@[simp] theorem ordinaryContentComp_mk (v t w : List I)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t))
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D w)) :
    ordinaryContentComp D Sc a v t w ((cycHom D Sc a v t).mkQ f) ((cycHom D Sc a t w).mkQ g) =
      (cycHom D Sc a v w).mkQ (f ≫ g) := rfl

instance ordinaryContentCategory (ν : List I) : Category (OrdinaryContentCategory D Sc a ν) where
  Hom v w := ((pres D Sc).obj (ob D v.word) ⟶ (pres D Sc).obj (ob D w.word)) ⧸ cycHom D Sc a v.word w.word
  id v := (cycHom D Sc a v.word v.word).mkQ (𝟙 _)
  comp {v t w} f g := ordinaryContentComp D Sc a v.word t.word w.word f g
  id_comp := by
    intro v w f
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word w.word).mkQ_surjective f
    exact congrArg (cycHom D Sc a v.word w.word).mkQ (Category.id_comp f)
  comp_id := by
    intro v w f
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word w.word).mkQ_surjective f
    exact congrArg (cycHom D Sc a v.word w.word).mkQ (Category.comp_id f)
  assoc := by
    intro v t w z f g h
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word t.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc a t.word w.word).mkQ_surjective g
    obtain ⟨h,rfl⟩ := (cycHom D Sc a w.word z.word).mkQ_surjective h
    exact congrArg (cycHom D Sc a v.word z.word).mkQ (Category.assoc f g h)

instance ordinaryContentPreadditive (ν : List I) : Preadditive (OrdinaryContentCategory D Sc a ν) where
  homGroup v w := inferInstanceAs (AddCommGroup (((pres D Sc).obj (ob D v.word) ⟶
    (pres D Sc).obj (ob D w.word)) ⧸ cycHom D Sc a v.word w.word))
  add_comp := by intro v w z f g h; exact LinearMap.map_add₂ (ordinaryContentComp D Sc a v.word w.word z.word) f g h
  comp_add := by intro v w z f g h; exact (ordinaryContentComp D Sc a v.word w.word z.word f).map_add g h

instance ordinaryContentLinear (ν : List I) : Linear k (OrdinaryContentCategory D Sc a ν) where
  homModule v w := inferInstanceAs (Module k (((pres D Sc).obj (ob D v.word) ⟶
    (pres D Sc).obj (ob D w.word)) ⧸ cycHom D Sc a v.word w.word))
  smul_comp := by intro v w z r f g; exact LinearMap.map_smul₂ (ordinaryContentComp D Sc a v.word w.word z.word) r f g
  comp_smul := by intro v w z f r g; exact (ordinaryContentComp D Sc a v.word w.word z.word f).map_smul r g

variable (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "probe" => probePolynomial (k := k) (probeDotExponent D) m
local notation "C" => ELV.OldContentCategory D Sc cut ν
local notation "Q" => OrdinaryContentCategory D Sc probe ν

/-- Actual scalar specialization, on the literal ordinary quotient category. -/
def probeOldOrdinaryFunctor : C ⥤ Q where
  obj v := ⟨v.obj.word,v.wordPerm⟩
  map {v w} := elvProbeOldHom D m Sc v.obj.word w.obj.word
  map_id v := by
    change (cycHom D Sc probe v.obj.word v.obj.word).mkQ
      (elvProbeScalarHom D m Sc v.obj.word v.obj.word (𝟙 (ELV.obj D Sc cut v.obj.word))) = _
    rw [elvProbeScalarHom_id]
    rfl
  map_comp {v t w} f g := by
    obtain ⟨f,rfl⟩ := (ELV.ideal D Sc cut v.obj.word t.obj.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (ELV.ideal D Sc cut t.obj.word w.obj.word).mkQ_surjective g
    change (cycHom D Sc probe v.obj.word w.obj.word).mkQ
      (elvProbeScalarHom D m Sc v.obj.word w.obj.word (f ≫ g)) =
      ordinaryContentComp D Sc probe v.obj.word t.obj.word w.obj.word
        ((cycHom D Sc probe v.obj.word t.obj.word).mkQ (elvProbeScalarHom D m Sc _ _ f))
        ((cycHom D Sc probe t.obj.word w.obj.word).mkQ (elvProbeScalarHom D m Sc _ _ g))
    rw [ordinaryContentComp_mk, elvProbeScalarHom_comp]

instance : (probeOldOrdinaryFunctor D Sc m ν).Full where
  map_surjective {v w} f := elvProbeOldHom_surjective D m Sc v.obj.word w.obj.word f
instance : (probeOldOrdinaryFunctor D Sc m ν).Additive where
  map_add {v w} f g := (elvProbeOldHom D m Sc v.obj.word w.obj.word).map_add f g
instance : (probeOldOrdinaryFunctor D Sc m ν).Linear k where
  map_smul {v w} f r := (elvProbeOldHom D m Sc v.obj.word w.obj.word).map_smul r f

/-- The same actual word, viewed in the source old content category. -/
def probeOrdinaryOldObject (v : Q) : C := ⟨⟨v.word⟩,v.wordPerm⟩

@[simp] theorem probeOldOrdinaryFunctor_obj_lift (v : Q) :
    (probeOldOrdinaryFunctor D Sc m ν).obj (probeOrdinaryOldObject D Sc m ν v) = v := by
  cases v
  rfl

variable
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

/-- The actual descended ordinary module on precisely the original old module values. -/
def probeOrdinaryModuleFunctor : Q ⥤ SVec k where
  obj v := N.obj (probeOrdinaryOldObject D Sc m ν v)
  map {v w} := probeOrdinaryModuleHom D m Sc ν N hN
    (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)
  map_id v := by
    change probeOldModuleRawAction D m Sc ν N
      (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν v)
      (ELV.affineUnit D Sc cut v.word v.word (𝟙 _)) = _
    rw [ELV.affineUnit_id]
    exact N.toFunctor.map_id _
  map_comp {v t w} f g := by
    obtain ⟨f,rfl⟩ := (cycHom D Sc probe v.word t.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc probe t.word w.word).mkQ_surjective g
    change probeOldModuleRawAction D m Sc ν N
      (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)
      (ELV.affineUnit D Sc cut v.word w.word (f ≫ g)) =
      probeOldModuleRawAction D m Sc ν N
        (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν t)
        (ELV.affineUnit D Sc cut v.word t.word f) ≫
      probeOldModuleRawAction D m Sc ν N
        (probeOrdinaryOldObject D Sc m ν t) (probeOrdinaryOldObject D Sc m ν w)
        (ELV.affineUnit D Sc cut t.word w.word g)
    rw [ELV.affineUnit_comp]
    exact N.toFunctor.map_comp
      (show probeOrdinaryOldObject D Sc m ν v ⟶ probeOrdinaryOldObject D Sc m ν t from
        (ELV.ideal D Sc cut v.word t.word).mkQ (ELV.affineUnit D Sc cut v.word t.word f))
      (show probeOrdinaryOldObject D Sc m ν t ⟶ probeOrdinaryOldObject D Sc m ν w from
        (ELV.ideal D Sc cut t.word w.word).mkQ (ELV.affineUnit D Sc cut t.word w.word g))

instance : (probeOrdinaryModuleFunctor D Sc m ν N hN).Additive where
  map_add {v w} f g := (probeOrdinaryModuleHom D m Sc ν N hN
    (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)).map_add f g
instance : (probeOrdinaryModuleFunctor D Sc m ν N hN).Linear k where
  map_smul {v w} f r := (probeOrdinaryModuleHom D m Sc ν N hN
    (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)).map_smul r f

/-- Restriction along the full scalar functor recovers the existing old module exactly. -/
theorem probeOrdinaryModuleFunctor_restrict :
    probeOldOrdinaryFunctor D Sc m ν ⋙ probeOrdinaryModuleFunctor D Sc m ν N hN = N.toFunctor := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro v
    rfl
  case h_map =>
    intro v w f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact probeOrdinaryModuleHom_old D m Sc ν N hN v w f

end OddMath.QuiverHecke
end

end

section

/-! # The literal commuting append square for scalar probe specialization
Ordinary right append acts on the existing cycHom quotients. The full scalar
functors commute with canonical old append exactly, providing the concrete
square for the induction-composition comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "C" => OrdinaryContentCategory D Sc a ν

/-- Right append on the literal ordinary quotient content category. -/
def probeOrdinaryAppend (i : I) : C ⥤ OrdinaryContentCategory D Sc a (i :: ν) where
  obj v := ⟨v.word ++ [i], (v.wordPerm.append (List.Perm.refl [i])).trans
    (List.perm_append_comm : (ν ++ [i]).Perm ([i] ++ ν))⟩
  map {v w} := probeCycHomRightContext D m Sc [i] v.word w.word
  map_id v := by
    change (cycHom D Sc a (v.word ++ [i]) (v.word ++ [i])).mkQ
      ((𝟙 ((pres D Sc).obj (ob D v.word))) ▷ ((pres D Sc).obj (ob D [i]))) = _
    exact congrArg (cycHom D Sc a (v.word ++ [i]) (v.word ++ [i])).mkQ
      (MonoidalSupercategory.id_whiskerRight (R := k) _ _)
  map_comp {v t w} f g := by
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word t.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc a t.word w.word).mkQ_surjective g
    change (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
      ((f ≫ g) ▷ ((pres D Sc).obj (ob D [i]))) =
      (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
        ((f ▷ ((pres D Sc).obj (ob D [i]))) ≫ (g ▷ ((pres D Sc).obj (ob D [i]))))
    exact congrArg (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
      (MonoidalSupercategory.comp_whiskerRight (R := k) f g _)

instance (i : I) : (probeOrdinaryAppend D Sc m ν i).Additive where
  map_add {v w} f g := (probeCycHomRightContext D m Sc [i] v.word w.word).map_add f g
instance (i : I) : (probeOrdinaryAppend D Sc m ν i).Linear k where
  map_smul {v w} f r := (probeCycHomRightContext D m Sc [i] v.word w.word).map_smul r f

/-- The square uses the actual old append, actual full scalar functors and
actual ordinary quotient append, with no assumed natural comparison. -/
theorem probeOldOrdinaryFunctor_append (i : I) :
    ELV.oldContentAppend D Sc cut ν i ⋙ probeOldOrdinaryFunctor D Sc m (i :: ν) =
      probeOldOrdinaryFunctor D Sc m ν ⋙ probeOrdinaryAppend D Sc m ν i := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro v
    rfl
  case h_map =>
    intro v w f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact elvProbeOldHom_rightContext D m Sc [i] v.obj.word w.obj.word f

end OddMath.QuiverHecke
end

end

section

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
    (f : ELV.hom D Sc cut v w) :
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
  have h := elvProbeAffineSpecialization_ideal D m Sc (ELV.ideal_proj_mem D Sc cut hg p)
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
    Superfunctor k (ELV.OldContentCategory D Sc cut ν) (OrdinaryContentCategory D Sc a ν) :=
  ⟨probeOldOrdinaryFunctor D Sc m ν⟩

variable (ν : List I)
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
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
end

end

section

/-! # Scalar quotient and ordinary probe append induction
The proved scalar-kernel closure, the full quotient counit and composition
of balanced induction identify old scalar append induction with literal
ordinary quotient append induction. No height-algebra identification or
weighted coefficient-truncation specialization is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "cut" => probeCutoff D m
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "C" => ELV.OldContentCategory D Sc cut ν
local notation "O" => OrdinaryContentCategory D Sc a ν

/-- Restriction uses the existing full scalar Superfunctor. -/
def probeOrdinaryRestriction (M : Superfunctor k O (SVec k)) : Superfunctor k C (SVec k) :=
  (probeOldOrdinarySuperfunctor D Sc m ν).comp M

variable (M : Superfunctor k (OrdinaryContentCategory D Sc
  (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))

private def probeQuotientCounitInverse (w : O) :
    M.obj w →ₗ[k] ELV.BalancedInduction.Obj Q (Q ⋙ M.toFunctor) w :=
  ELV.BalancedInduction.unit Q (Q ⋙ M.toFunctor) (probeOrdinaryOldObject D Sc m ν w)

private theorem probeQuotientCounit_right_inv (w : O) :
    (ELV.BalancedInduction.counit Q M.toFunctor w).comp
      (probeQuotientCounitInverse D Sc m ν M w) = LinearMap.id :=
  ELV.BalancedInduction.counit_unit Q M.toFunctor (probeOrdinaryOldObject D Sc m ν w)

private theorem probeQuotientCounit_left_inv (w : O) :
    (probeQuotientCounitInverse D Sc m ν M w).comp
      (ELV.BalancedInduction.counit Q M.toFunctor w) = LinearMap.id :=
  ELV.BalancedInduction.unit_counit_of_full Q M.toFunctor (probeOrdinaryOldObject D Sc m ν w)

/-- The full scalar quotient counit is an even isomorphism on modules. -/
def probeQuotientCounitIso :
    ELV.BalancedInduction.induced Q (probeOrdinaryRestriction D Sc m ν M) ≅ M :=
  ELV.moduleIsoOfEvenNatIso _ _
    (NatIso.ofComponents (fun w =>
      { hom := ELV.BalancedInduction.counit Q M.toFunctor w
        inv := probeQuotientCounitInverse D Sc m ν M w
        hom_inv_id := probeQuotientCounit_left_inv D Sc m ν M w
        inv_hom_id := probeQuotientCounit_right_inv D Sc m ν M w })
      (fun f => ELV.BalancedInduction.counit_naturality Q M.toFunctor f))
    (fun w => ELV.BalancedInduction.counit_mem Q M w)
    (fun w => ELV.BalancedInduction.unit_mem Q (probeOrdinaryRestriction D Sc m ν M)
      (probeOrdinaryOldObject D Sc m ν w))

variable
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

/-- The scalar-evaluated old module has precisely its descended ordinary induction. -/
def probeQuotientInducedModuleIso :
    ELV.BalancedInduction.induced Q N ≅ probeOrdinaryModuleSuperfunctor D Sc m ν N hN :=
  ((ELV.BalancedInduction.induction Q).mapIso
    (eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN))).symm ≪≫
      probeQuotientCounitIso D Sc m ν (probeOrdinaryModuleSuperfunctor D Sc m ν N hN)

/-- Actual old append induction, descended by proved scalar-kernel closure,
agrees with literal ordinary append induction of the descended module. -/
def probeAppendOrdinaryModuleIso (i : I) :
    probeOrdinaryModuleSuperfunctor D Sc m (i :: ν)
      (ELV.BalancedInduction.induced (ELV.oldContentAppend D Sc cut ν i) N)
      (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN) ≅
    ELV.BalancedInduction.induced (probeOrdinaryAppend D Sc m ν i)
      (probeOrdinaryModuleSuperfunctor D Sc m ν N hN) :=
  let J := ELV.oldContentAppend D Sc cut ν i
  let T := probeOrdinaryAppend D Sc m ν i
  let U := probeOldOrdinaryFunctor D Sc m (i :: ν)
  let L := ELV.BalancedInduction.induced J N
  let hL := probeOldInduced_evaluatesCoefficients D m Sc ν i N hN
  (probeQuotientInducedModuleIso D Sc m (i :: ν) L hL).symm ≪≫
    (ELV.BalancedInduction.inductionComp J U).app N ≪≫
      ELV.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T)
        (probeOldOrdinaryFunctor_append D Sc m ν i) N ≪≫
      ((ELV.BalancedInduction.inductionComp Q T).app N).symm ≪≫
      (ELV.BalancedInduction.induction T).mapIso
        (probeQuotientInducedModuleIso D Sc m ν N hN)

end OddMath.QuiverHecke
end

end
