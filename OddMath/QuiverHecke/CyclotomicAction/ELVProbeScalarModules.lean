import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldModule
import OddMath.QuiverHecke.CyclotomicAction.ELVPScalarBalance
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction

/-! # Scalar-evaluated actual old probe modules
The coefficient condition is proved for the actual probe module. It then
forces every old module map to factor through the prescribed scalar Hom
specialization, directly by the tensor universal property, without a flatness premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k)
local notation "cut" => probeCutoff D m
local notation "A" => SKM.SYM.ELVCoefficientAlgebra (k := k) D cut
local notation "ev" => SKM.SYM.elvScalarEvaluation D cut (probeScalarValues D m) (probeScalarValues_vanish D m)
variable (ν : List I)
local notation "C" => ELVOld.OldContentCategory D Sc cut ν

/-- The actual full coefficient at an old-content word identity. -/
def probeOldCoefficient (v : C) (c : A) : v ⟶ v :=
  (ELVOld.ideal D Sc cut v.obj.word v.obj.word).mkQ (c ⊗ₜ[k] (𝟙 _))

/-- Scalar evaluation of coefficients, as a property of the actual old module. -/
def ProbeEvaluatesCoefficients
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k)) : Prop :=
  ∀ (v : C) (c : A), N.toFunctor.map (probeOldCoefficient D m Sc ν v c) = ev c • 𝟙 (N.obj v)

omit ν in
/-- The scalar Hom map evaluates an arbitrary pure coefficient tensor literally. -/
theorem elvProbeScalarHom_tmul {v w : List I} (c : A)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    elvProbeScalarHom D m Sc v w (c ⊗ₜ[k] f) = ev c • f := by
  change (elvAffineScalarSpecialization D Sc cut (probeScalarValues D m)
    (probeScalarValues_vanish D m)).map
      (BoxProd.tmulHom (X := ELVOld.obj D Sc cut v) (Y := ELVOld.obj D Sc cut w)
        (SuperalgebraCat.ofElem c) f) = _
  rw [elvAffineScalarSpecialization_tmul, SuperalgebraCat.toElem_ofElem]

variable
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))

/-- The existing old module action on raw full-coefficient Homs. -/
def probeOldModuleRawAction (v w : C) :
    ELVOld.hom D Sc cut v.obj.word w.obj.word →ₗ[k] (N.obj v ⟶ N.obj w) :=
  (N.toFunctor.mapLinearMap k (X := v) (Y := w)).comp
    (ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ

@[simp] theorem probeOldModuleRawAction_apply (v w : C)
    (f : ELVOld.hom D Sc cut v.obj.word w.obj.word) :
    probeOldModuleRawAction D m Sc ν N v w f =
      N.toFunctor.map (show v ⟶ w from
        (ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ f) := rfl

/-- Coefficient evaluation forces raw module action to factor through the
actual scalar specialization. No tensor-kernel or flatness assumption is used. -/
theorem probeOldModuleRawAction_factor (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (v w : C) (f : ELVOld.hom D Sc cut v.obj.word w.obj.word) :
    probeOldModuleRawAction D m Sc ν N v w f =
      probeOldModuleRawAction D m Sc ν N v w
        (ELVOld.affineUnit D Sc cut v.obj.word w.obj.word
          (elvProbeScalarHom D m Sc v.obj.word w.obj.word f)) := by
  have hlin : probeOldModuleRawAction D m Sc ν N v w =
      ((probeOldModuleRawAction D m Sc ν N v w).comp
        (ELVOld.affineUnit D Sc cut v.obj.word w.obj.word)).comp
          (elvProbeScalarHom D m Sc v.obj.word w.obj.word) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro g
    change A at c
    change ((pres D Sc).obj (ob D v.obj.word) ⟶ (pres D Sc).obj (ob D w.obj.word)) at g
    change probeOldModuleRawAction D m Sc ν N v w (c ⊗ₜ[k] g) =
      probeOldModuleRawAction D m Sc ν N v w
        (ELVOld.affineUnit D Sc cut v.obj.word w.obj.word
          (elvProbeScalarHom D m Sc v.obj.word w.obj.word (c ⊗ₜ[k] g)))
    have hraw : ELVOld.affineUnit D Sc cut v.obj.word w.obj.word g ≫
        (c ⊗ₜ[k] (𝟙 ((pres D Sc).obj (ob D w.obj.word))) : ELVOld.hom D Sc cut w.obj.word w.obj.word) =
          (c ⊗ₜ[k] g : ELVOld.hom D Sc cut v.obj.word w.obj.word) := by
      simpa only [Category.comp_id] using
        (ELVOld.affineUnit_comp_coefficient D Sc cut (v := v.obj.word) (w := w.obj.word) (z := w.obj.word)
          g (𝟙 ((pres D Sc).obj (ob D w.obj.word))) c)
    have hcomp : (show v ⟶ w from
        (ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ (c ⊗ₜ[k] g)) =
      (show v ⟶ w from
        (ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ
          (ELVOld.affineUnit D Sc cut v.obj.word w.obj.word g)) ≫
            probeOldCoefficient D m Sc ν w c :=
      congrArg (ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ hraw.symm
    rw [probeOldModuleRawAction_apply, hcomp, N.toFunctor.map_comp, hN w c]
    rw [elvProbeScalarHom_tmul, map_smul, map_smul]
    rw [Linear.comp_smul, Category.comp_id]
    rfl
  exact LinearMap.congr_fun hlin f

variable [Fintype I]

theorem probeOldCoefficient_image (v : C) (c : A) :
    probeOldWordEntry D m Sc ν (probeOldCoefficient D m Sc ν v c) =
      ev c • probeOldWordIdempotent D m Sc ν v := by
  change probeHeightMk D m Sc ν.length
    (FiniteHomMatrix.single (⟨v.obj.word,v.wordPerm.length_eq⟩ : Word I ν.length)
      (⟨v.obj.word,v.wordPerm.length_eq⟩ : Word I ν.length)
      (elvProbeScalarHom D m Sc v.obj.word v.obj.word
        (c ⊗ₜ[k] (𝟙 ((pres D Sc).obj (ob D v.obj.word)))))) = _
  rw [elvProbeScalarHom_tmul, FiniteHomMatrix.single_smul, map_smul]
  rfl

variable {B : Type u} [Ring B] [Algebra k B] {GB : ZMod 2 → Submodule k B}
  (M : SuperBimodule
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) ν.length) GB)

/-- The concrete probe module satisfies the scalar coefficient condition. -/
theorem probeOldModule_evaluatesCoefficients :
    ProbeEvaluatesCoefficients D m Sc ν (probeOldModule D m Sc ν M) := by
  intro v c
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change M.lact (probeOldWordEntry D m Sc ν (probeOldCoefficient D m Sc ν v c)) x.val =
    ev c • x.val
  rw [probeOldCoefficient_image, map_smul]
  change ev c • M.lact (probeOldWordIdempotent D m Sc ν v) x.val = ev c • x.val
  rw [x.property]

end OddMath.QuiverHecke

