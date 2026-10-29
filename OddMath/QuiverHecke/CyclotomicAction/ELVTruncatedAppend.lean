/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedCategory
import OddMath.QuiverHecke.CyclotomicAction.ELVOldRightContext
import StringDiagrams.Super.GSCat

/-! # Right append on the coefficient-truncated ELV category

Right contexts preserve both the first-position cyclotomic ideal and the
coefficient weight ideal. The resulting functors use the original signed
coefficient composition; no left-context stability is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

@[simp] theorem rightContext_id (σ v : List I) :
    rightContext D Sc cutoff σ v v (𝟙 (obj D Sc cutoff v)) =
      𝟙 (obj D Sc cutoff (v ++ σ)) := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    ((𝟙 ((pres D Sc).obj (ob D v))) ▷ (pres D Sc).obj (ob D σ)) = _
  rw [MonoidalSupercategory.id_whiskerRight (R := k)]
  rfl

@[simp] theorem rightContext_coefficientIdentity (σ t : List I) (a : SKM.SYM D k) :
    rightContext D Sc cutoff σ t t (coefficientIdentity D Sc cutoff t a) =
      coefficientIdentity D Sc cutoff (t ++ σ) a := by
  change SKM.SYM.elvCoefficientQuotient D cutoff a ⊗ₜ[k]
    ((𝟙 ((pres D Sc).obj (ob D t))) ▷ (pres D Sc).obj (ob D σ)) = _
  rw [MonoidalSupercategory.id_whiskerRight (R := k)]
  rfl

/-- Coefficient weights do not change when spectator strands are appended. -/
theorem coefficientHomIdeal_rightContext (N : ℕ) (σ : List I)
    {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ coefficientHomIdeal D Sc cutoff N v w) :
    rightContext D Sc cutoff σ v w f ∈
      coefficientHomIdeal D Sc cutoff N (v ++ σ) (w ++ σ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t, a, ha, l, r, rfl⟩ := hf
    rw [rightContext_comp, rightContext_comp, rightContext_coefficientIdentity]
    exact Submodule.subset_span ⟨t ++ σ, a, ha,
      rightContext D Sc cutoff σ v t l, rightContext D Sc cutoff σ t w r, rfl⟩
  | zero => simpa only [map_zero] using
      (coefficientHomIdeal D Sc cutoff N (v ++ σ) (w ++ σ)).zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [map_smul] using Submodule.smul_mem _ c hf

theorem truncatedIdeal_rightContext (N : ℕ) (σ : List I)
    {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ truncatedIdeal D Sc cutoff N v w) :
    rightContext D Sc cutoff σ v w f ∈
      truncatedIdeal D Sc cutoff N (v ++ σ) (w ++ σ) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨_, ideal_rightContext D Sc cutoff σ ha,
    _, coefficientHomIdeal_rightContext D Sc cutoff N σ hb, rfl⟩

variable (N : ℕ)

/-- Right extension on the two-ideal quotient. -/
def truncatedRightContext (σ v w : List I) :
    TruncatedOld D Sc cutoff N v w →ₗ[k]
      TruncatedOld D Sc cutoff N (v ++ σ) (w ++ σ) :=
  (truncatedIdeal D Sc cutoff N v w).mapQ
    (truncatedIdeal D Sc cutoff N (v ++ σ) (w ++ σ))
    (rightContext D Sc cutoff σ v w)
    (fun _ hf => truncatedIdeal_rightContext D Sc cutoff N σ hf)

@[simp] theorem truncatedRightContext_mk (σ v w : List I) (f : hom D Sc cutoff v w) :
    truncatedRightContext D Sc cutoff N σ v w
      ((truncatedIdeal D Sc cutoff N v w).mkQ f) =
      (truncatedIdeal D Sc cutoff N (v ++ σ) (w ++ σ)).mkQ
        (rightContext D Sc cutoff σ v w f) := rfl

/-- Append an arbitrary word, without changing coefficients or their cutoff. -/
def truncatedAppend (σ : List I) :
    TruncatedCategory D Sc cutoff N ⥤ TruncatedCategory D Sc cutoff N where
  obj v := ⟨v.word ++ σ⟩
  map {v w} := truncatedRightContext D Sc cutoff N σ v.word w.word
  map_id v := congrArg (truncatedIdeal D Sc cutoff N _ _).mkQ
    (rightContext_id D Sc cutoff σ v.word)
  map_comp {v w z} f g := by
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (truncatedIdeal D Sc cutoff N w.word z.word).mkQ_surjective g
    exact congrArg (truncatedIdeal D Sc cutoff N _ _).mkQ
      (rightContext_comp D Sc cutoff σ f g)

instance truncatedAppend_additive (σ : List I) :
    (truncatedAppend D Sc cutoff N σ).Additive where
  map_add := map_add (truncatedRightContext D Sc cutoff N σ _ _) _ _

instance truncatedAppend_linear (σ : List I) :
    Functor.Linear k (truncatedAppend D Sc cutoff N σ) where
  map_smul f c := map_smul (truncatedRightContext D Sc cutoff N σ _ _) c f

theorem rightContext_proj (σ : List I) {v w : List I} (p : ZMod 2)
    (f : hom D Sc cutoff v w) :
    rightContext D Sc cutoff σ v w (Supercategory.proj k p f) =
      Supercategory.proj k p (rightContext D Sc cutoff σ v w f) := by
  induction f using BoxProd.induction_on_homogeneous with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul q r a f ha hf =>
    have hs := BoxProd.tmul_mem_parity ha hf
    have ht := BoxProd.tmul_mem_parity (X := obj D Sc cutoff (v ++ σ))
      (Y := obj D Sc cutoff (w ++ σ)) ha
      (MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D σ)) hf)
    by_cases h : q + r = p
    · subst p
      rw [Supercategory.proj_of_mem hs]
      exact (Supercategory.proj_of_mem ht).symm
    · rw [Supercategory.proj_of_mem_ne hs h, map_zero]
      exact (Supercategory.proj_of_mem_ne ht h).symm

theorem rightContext_mem_parity (σ : List I) {v w : List I} {p : ZMod 2}
    {f : hom D Sc cutoff v w}
    (hf : f ∈ Supercategory.parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) p) :
    rightContext D Sc cutoff σ v w f ∈ Supercategory.parity (R := k)
      (obj D Sc cutoff (v ++ σ)) (obj D Sc cutoff (w ++ σ)) p := by
  apply Supercategory.mem_iff_proj.mpr
  rw [← rightContext_proj, Supercategory.proj_of_mem hf]

instance truncatedAppend_super (σ : List I) :
    IsSuperfunctor k (truncatedAppend D Sc cutoff N σ) where
  map_mem := by
    rintro v w p f ⟨a, ha, rfl⟩
    exact Submodule.mem_map_of_mem (rightContext_mem_parity D Sc cutoff σ ha)

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

theorem rightContext_mem_degree (σ : List I) {v w : List I} {n : ℤ}
    {f : hom D Sc cutoff v w} (hf : f ∈ elvHomDegree D sy Sc hc cutoff v w n) :
    rightContext D Sc cutoff σ v w f ∈
      elvHomDegree D sy Sc hc cutoff (v ++ σ) (w ++ σ) n := by
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  let _ := gradedMonoidalSupercategory D sy Sc hc
  refine BoxProd.map_mem_of_homDeg (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w) (rightContext D Sc cutoff σ v w) _ ?_ hf
  intro r s hrs a ha g hg
  subst n
  exact BoxProd.tmulHom_mem_degree (X := obj D Sc cutoff (v ++ σ))
    (Y := obj D Sc cutoff (w ++ σ)) ha
    (GradedMonoidalSupercategory.whiskerRight_mem_degree ((pres D Sc).obj (ob D σ)) hg)

/-- Right append has degree zero, independently of total super parity. -/
theorem truncatedAppend_mem_degree (σ : List I)
    {v w : TruncatedCategory D Sc cutoff N} {n : ℤ} {f : v ⟶ w}
    (hf : f ∈ truncatedDegree D Sc cutoff sy hc N v.word w.word n) :
    (truncatedAppend D Sc cutoff N σ).map f ∈
      truncatedDegree D Sc cutoff sy hc N (v.word ++ σ) (w.word ++ σ) n := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact Submodule.mem_map_of_mem (rightContext_mem_degree D Sc cutoff sy hc σ ha)

/-- The graded superfunctor appending an arbitrary word. -/
def truncatedAppendGraded (σ : List I) :
    letI := truncatedGradedSupercategory D Sc cutoff N sy hc
    GradedSuperfunctor k (TruncatedCategory D Sc cutoff N) (TruncatedCategory D Sc cutoff N) := by
  letI := truncatedGradedSupercategory D Sc cutoff N sy hc
  exact { toFunctor := truncatedAppend D Sc cutoff N σ
          isGraded := { map_mem_degree := truncatedAppend_mem_degree D Sc cutoff N sy hc σ } }

end OddMath.QuiverHecke.ELVOld
