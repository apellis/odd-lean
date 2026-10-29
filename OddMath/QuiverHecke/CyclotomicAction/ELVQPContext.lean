/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVQPOdd

/-!
# QP right-context descent over ELV coefficients

Supporting steps for `DeformedGlobalQP.md` §3, in the library's signed crossing
convention. Spectator extension descends to the old-only quotient, with the full
coefficient algebra unchanged. The distinct-colour recursion and empty-word base
use the same evaluation as the repeated-colour recursions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Right spectators preserve the defining relation submodule, not merely the old ideal. -/
theorem relations_rightContext (σ : List I) (i : I) {v w : List I}
    {f : hom D Sc cutoff (i :: v) w} (hf : f ∈ relations D Sc cutoff i v w) :
    rightContext D Sc cutoff σ (i :: v) w f ∈
      relations D Sc cutoff i (v ++ σ) (w ++ σ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t, r, hr, h, rfl⟩ := hf
    rw [rightContext_comp, rightContext_insert]
    exact Submodule.subset_span ⟨t ++ σ, _, ideal_rightContext D Sc cutoff σ hr, _, rfl⟩
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [map_smul] using Submodule.smul_mem _ c hf

/-- Spectator extension on the old-only quotient. -/
def targetRightContext (σ : List I) (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i (v ++ σ) (w ++ σ) :=
  (relations D Sc cutoff i v w).mapQ
    (relations D Sc cutoff i (v ++ σ) (w ++ σ))
    (rightContext D Sc cutoff σ (i :: v) w)
    (fun _ hf => relations_rightContext D Sc cutoff σ i hf)

@[simp] theorem targetRightContext_projection (σ : List I) (i : I) (v w : List I)
    (f : hom D Sc cutoff (i :: v) w) :
    targetRightContext D Sc cutoff σ i v w (projection D Sc cutoff i v w f) =
      projection D Sc cutoff i (v ++ σ) (w ++ σ)
        (rightContext D Sc cutoff σ (i :: v) w f) := rfl

/-- An equality in the smaller quotient remains true after adjoining spectators and
an arbitrary full-coefficient continuation. -/
theorem projection_rightContext_eq (σ : List I) (i : I) {v w z : List I}
    (f g : hom D Sc cutoff (i :: v) w)
    (hfg : projection D Sc cutoff i v w f = projection D Sc cutoff i v w g)
    (h : hom D Sc cutoff (w ++ σ) z) :
    projection D Sc cutoff i (v ++ σ) z
        (rightContext D Sc cutoff σ (i :: v) w f ≫ h) =
      projection D Sc cutoff i (v ++ σ) z
        (rightContext D Sc cutoff σ (i :: v) w g ≫ h) :=
  congrArg (fun x => act D Sc cutoff i h (targetRightContext D Sc cutoff σ i v w x)) hfg

/-- The QP induction hypothesis descends from its smaller quotient to every right
context and arbitrary continuation. No quotient-stability premise is assumed. -/
theorem qpEval_of_projection_eq (i : I) (μ σ z : List I)
    (f g : End ((pres D Sc).obj (ob D (i :: μ))))
    (hfg : projection D Sc cutoff i μ (i :: μ)
        (affineUnit D Sc cutoff _ _ f ≫ relation D Sc cutoff i μ) =
      projection D Sc cutoff i μ (i :: μ)
        (affineUnit D Sc cutoff _ _ g ≫ relation D Sc cutoff i μ))
    (h : hom D Sc cutoff ((i :: μ) ++ σ) z) :
    qpEval D Sc cutoff i μ σ z h f = qpEval D Sc cutoff i μ σ z h g := by
  have he := projection_rightContext_eq D Sc cutoff σ i _ _ hfg h
  rw [rightContext_comp, rightContext_comp, rightContext_relation,
    Category.assoc, Category.assoc] at he
  exact he

/-- Distinct-colour recursion, with arbitrary spectators and full ELV continuation. -/
theorem qp_distinct (i x : I) (hx : i ≠ x) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: (μ ++ [x])) ++ σ) z) :
    qpEval D Sc cutoff i (μ ++ [x]) σ z h
      (moveHom D Sc i [] (μ ++ [x]) ≫ lastToFirstHom D Sc i (μ ++ [x])) =
    qpEval D Sc cutoff i (μ ++ [x]) σ z h
      (qPoly D Sc (dotE D Sc (i :: (μ ++ [x])) 0)
        (dotE D Sc (i :: (μ ++ [x])) (μ.length + 1)) i x ≫
        ((moveHom D Sc i [] μ ≫ lastToFirstHom D Sc i μ) ▷ (pres D Sc).obj (ob D [x]))) := by
  rw [moveHom_lastToFirstHom_append_ne D Sc hx μ]

/-- Empty-word base with the actual signed product and arbitrary continuation. -/
theorem qp_nil (i : I) (σ z : List I) (h : hom D Sc cutoff (i :: σ) z) :
    qpEval D Sc cutoff i [] σ z h
      (moveHom D Sc i [] [] ≫ lastToFirstHom D Sc i []) =
      qpEval D Sc cutoff i [] σ z h (qpProduct D Sc i []) := by
  congr 1
  simp [moveHom, lastToFirstHom, qpProduct, End.one_def]

end OddMath.QuiverHecke.ELVOld
