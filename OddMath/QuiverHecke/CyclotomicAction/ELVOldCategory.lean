/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPCentral
import OddMath.QuiverHecke.FiniteHomMatrixRightModule
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-! # Ordinary old ELV quotient category

The old cyclotomic Hom quotients form a linear category. Its finite content
Hom matrices give the ordinary coefficient ring in the square resolution.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Words in the old cyclotomic ELV category. -/
structure OldCategory (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (cutoff : I → ℕ) where
  word : List I

/-- Quotient composition, in categorical order. -/
def oldComp (v t w : List I) :
    Old D Sc cutoff v t →ₗ[k]
      Old D Sc cutoff t w →ₗ[k] Old D Sc cutoff v w :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun f =>
        { toFun := fun g => (ideal D Sc cutoff v w).mkQ (f ≫ g)
          map_add' := by intros; simp only [Preadditive.comp_add, map_add]
          map_smul' := by intros; simp only [Linear.comp_smul, map_smul, RingHom.id_apply] }
       map_add' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk, Preadditive.add_comp, map_add, LinearMap.add_apply]
       map_smul' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk, Linear.smul_comp, map_smul, LinearMap.smul_apply, RingHom.id_apply] } :
       hom D Sc cutoff v t →ₗ[k] hom D Sc cutoff t w →ₗ[k] Old D Sc cutoff v w)
    (by
      intro f hf
      ext g
      exact (Submodule.Quotient.mk_eq_zero _).mpr (ideal_comp D Sc cutoff hf g))
    (by
      intro g hg
      ext f
      exact (Submodule.Quotient.mk_eq_zero _).mpr (comp_ideal D Sc cutoff f hg))

@[simp] theorem oldComp_mk (v t w : List I)
    (f : hom D Sc cutoff v t) (g : hom D Sc cutoff t w) :
    oldComp D Sc cutoff v t w
      ((ideal D Sc cutoff v t).mkQ f)
      ((ideal D Sc cutoff t w).mkQ g) =
      (ideal D Sc cutoff v w).mkQ (f ≫ g) := rfl

instance oldCategory : Category (OldCategory D Sc cutoff) where
  Hom v w := Old D Sc cutoff v.word w.word
  id v := (ideal D Sc cutoff v.word v.word).mkQ (𝟙 _)
  comp {v t w} f g := oldComp D Sc cutoff v.word t.word w.word f g
  id_comp := by
    intro v w f
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
    exact congrArg (ideal D Sc cutoff v.word w.word).mkQ (Category.id_comp f)
  comp_id := by
    intro v w f
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
    exact congrArg (ideal D Sc cutoff v.word w.word).mkQ (Category.comp_id f)
  assoc := by
    intro v t w z f g h
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff t.word w.word).mkQ_surjective g
    obtain ⟨h, rfl⟩ := (ideal D Sc cutoff w.word z.word).mkQ_surjective h
    exact congrArg (ideal D Sc cutoff v.word z.word).mkQ (Category.assoc f g h)

instance oldPreadditive : Preadditive (OldCategory D Sc cutoff) where
  homGroup v w := inferInstanceAs (AddCommGroup (Old D Sc cutoff v.word w.word))
  add_comp := by
    intro v t w f g h
    exact LinearMap.map_add₂ (oldComp D Sc cutoff v.word t.word w.word) f g h
  comp_add := by
    intro v t w f g h
    exact (oldComp D Sc cutoff v.word t.word w.word f).map_add g h

instance oldLinear : Linear k (OldCategory D Sc cutoff) where
  homModule v w := inferInstanceAs (Module k (Old D Sc cutoff v.word w.word))
  smul_comp := by
    intro v t w r f g
    exact LinearMap.map_smul₂ (oldComp D Sc cutoff v.word t.word w.word) r f g
  comp_smul := by
    intro v t w f r g
    exact (oldComp D Sc cutoff v.word t.word w.word f).map_smul r g


end OddMath.QuiverHecke.ELVOld
