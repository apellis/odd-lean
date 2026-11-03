/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCorrectedInductionBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldNestedMulticolourBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionTriplePolynomialMaps

/-! # The normalized corrected braid on nested OLD induction

Brundan–Ellis (1.9): compare the independently chosen nested crossings
through the six prescribed triple-flattening squares, and retain the
ordered original-Sc polynomial in the three independent nested dots.
The acting category uses parameterTwist Sc. No braid, naturality,
comparison or inverse premise is supplied.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction
universe u

private theorem signed_path_total
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {M A B : Superfunctor k C (SVec k)}
    (f₀ : M ⟶ A) (f₁ : End A) (f₂ : A ⟶ M)
    (g₀ : M ⟶ B) (g₁ : End B) (g₂ : B ⟶ M) (w : C) :
    (f₀ ≫ (-f₁) ≫ f₂ - g₀ ≫ (-g₁) ≫ g₂).total w =
      f₂.total w ∘ₗ (-f₁.total w) ∘ₗ f₀.total w -
        g₂.total w ∘ₗ (-g₁.total w) ∘ₗ g₀.total w := by
  have hsub {P Q : Superfunctor k C (SVec k)} (f g : P ⟶ Q) :
      (f - g).total w = f.total w - g.total w := by
    simp only [SuperNatTrans.total, Superfunctor.sub_app]
    abel
  have hneg {P Q : Superfunctor k C (SVec k)} (f : P ⟶ Q) :
      (-f).total w = -f.total w := by
    simp only [SuperNatTrans.total, Superfunctor.neg_app, neg_add]
  simp only [hsub, Superfunctor.comp_total, hneg]
  rfl

private theorem corrected_transform_total
    {k C B : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ)
    (N : Superfunctor k C (SVec k)) (w : B) :
    (transformComponent hγ N).total w = transformLinear hγ N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

private theorem scalar_total
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (d : k) (f : M ⟶ N) (w : C) :
    (d • f).total w = d • f.total w := by
  simp only [SuperNatTrans.total, Superfunctor.smul_app, smul_add]

private theorem compose_three_squares {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C}
    (e₀ : X₀ ⟶ Y₀) (e₁ : X₁ ⟶ Y₁) (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃)
    (a₀ : X₀ ⟶ X₁) (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₀ : Y₀ ⟶ Y₁) (b₁ : Y₁ ⟶ Y₂) (b₂ : Y₂ ⟶ Y₃)
    (h₀ : a₀ ≫ e₁ = e₀ ≫ b₀) (h₁ : a₁ ≫ e₂ = e₁ ≫ b₁)
    (h₂ : a₂ ≫ e₃ = e₂ ≫ b₂) :
    (a₀ ≫ a₁ ≫ a₂) ≫ e₃ = e₀ ≫ (b₀ ≫ b₁ ≫ b₂) := by
  simp only [Category.assoc]
  rw [h₂, ← Category.assoc a₁, h₁, Category.assoc e₁,
    ← Category.assoc a₀, h₀, Category.assoc]

private theorem negative_square {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (a : End X) (e : X ⟶ Y) (b : End Y)
    (h : a ≫ e = e ≫ b) : (-a) ≫ e = e ≫ (-b) := by
  rw [Preadditive.neg_comp, Preadditive.comp_neg, h]

private theorem difference_square {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (a b : End X) (c d : End Y) (e : X ⟶ Y)
    (ha : a ≫ e = e ≫ c) (hb : b ≫ e = e ≫ d) :
    (a - b) ≫ e = e ≫ (c - d) := by
  rw [Preadditive.sub_comp, Preadditive.comp_sub, ha, hb]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local notation "A" i => append D Sc cutoff i

/-- The prescribed normalized direct paths, as one entire module morphism. -/
def oldDirectMixedBraidMap (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    End (induced (tripleAppend D Sc cutoff i j i) N) :=
  transformComponent (tripleSuffix_supernatural D Sc cutoff i i j) N ≫
    (-transformComponent (triplePrefix_supernatural D Sc cutoff i i j) N) ≫
      transformComponent (tripleSuffix_supernatural D Sc cutoff i j i) N -
  transformComponent (triplePrefix_supernatural D Sc cutoff j i i) N ≫
    (-transformComponent (tripleSuffix_supernatural D Sc cutoff j i i) N) ≫
      transformComponent (triplePrefix_supernatural D Sc cutoff i j i) N

theorem oldDirectMixedBraidMap_total (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (w : OldCategory D Sc cutoff) :
    (oldDirectMixedBraidMap D Sc cutoff i j N).total w = oldDirectMixedBraid D Sc cutoff i j N w := by
  unfold oldDirectMixedBraidMap
  rw [signed_path_total]
  simp only [corrected_transform_total, oldDirectMixedBraid]

/-- The whole direct corrected path is the balanced transform of the literal coefficient correction. -/
theorem oldDirectMixedBraidMap_coefficient {i j : I} (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D (parameterTwist D Sc) cutoff) (SVec k)) :
    oldDirectMixedBraidMap D (parameterTwist D Sc) cutoff i j N =
      sign k (D.parity i * D.parity j) •
        transformComponent (tripleCorrection_supernatural D (parameterTwist D Sc) cutoff hij) N := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  rw [oldDirectMixedBraidMap_total, scalar_total, corrected_transform_total,
    oldDirectMixedBraid_polynomial D Sc cutoff hij N w, oldTriplePolynomial_operator D Sc cutoff hij N w]

/-- The two independent nested crossing paths, with the middle equal crossing negative. -/
def oldNestedMixedBraidMap (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    End ((induction (A i)).obj ((induction (A j)).obj ((induction (A i)).obj N))) :=
  (show End ((induction (A i)).obj ((induction (A j)).obj ((induction (A i)).obj N))) from
    nestedSuffix D Sc cutoff i j i N ≫ (-nestedPrefix D Sc cutoff i i j N) ≫
      nestedSuffix D Sc cutoff i i j N) -
    (show End ((induction (A i)).obj ((induction (A j)).obj ((induction (A i)).obj N))) from
      nestedPrefix D Sc cutoff i j i N ≫ (-nestedSuffix D Sc cutoff j i i N) ≫
        nestedPrefix D Sc cutoff j i i N)


/-- The six chosen crossing squares transport the entire normalized braid difference. -/
theorem oldNestedMixedBraidMap_conjugate (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    oldNestedMixedBraidMap D Sc cutoff i j N =
      inductionEndConjugation (k := k) (inductionTripleFlattening (A i) (A j) (A i) N)
        (oldDirectMixedBraidMap D Sc cutoff i j N) := by
  let e := inductionTripleFlattening (A i) (A j) (A i) N
  let eR := inductionTripleFlattening (A i) (A i) (A j) N
  let eL := inductionTripleFlattening (A j) (A i) (A i) N
  have hR := compose_three_squares e.hom eR.hom eR.hom e.hom
    (nestedSuffix D Sc cutoff i j i N) (-nestedPrefix D Sc cutoff i i j N)
    (nestedSuffix D Sc cutoff i i j N)
    (transformComponent (tripleSuffix_supernatural D Sc cutoff i i j) N)
    (-transformComponent (triplePrefix_supernatural D Sc cutoff i i j) N)
    (transformComponent (tripleSuffix_supernatural D Sc cutoff i j i) N)
    (nestedSuffix_flatten D Sc cutoff i j i N)
    (negative_square _ _ _ (nestedPrefix_flatten D Sc cutoff i i j N))
    (nestedSuffix_flatten D Sc cutoff i i j N)
  have hL := compose_three_squares e.hom eL.hom eL.hom e.hom
    (nestedPrefix D Sc cutoff i j i N) (-nestedSuffix D Sc cutoff j i i N)
    (nestedPrefix D Sc cutoff j i i N)
    (transformComponent (triplePrefix_supernatural D Sc cutoff j i i) N)
    (-transformComponent (tripleSuffix_supernatural D Sc cutoff j i i) N)
    (transformComponent (triplePrefix_supernatural D Sc cutoff i j i) N)
    (nestedPrefix_flatten D Sc cutoff i j i N)
    (negative_square _ _ _ (nestedSuffix_flatten D Sc cutoff j i i N))
    (nestedPrefix_flatten D Sc cutoff j i i N)
  have hrow : oldNestedMixedBraidMap D Sc cutoff i j N ≫ e.hom =
      e.hom ≫ oldDirectMixedBraidMap D Sc cutoff i j N :=
    difference_square _ _ _ _ _ hR hL
  exact (inductionEndConjugation_of_square e _ _ hrow).symm

/-- The entire nested corrected braid is the original-Sc polynomial in the three independent dots. -/
theorem oldNestedMixedBraidMap_polynomial {i j : I} (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D (parameterTwist D Sc) cutoff) (SVec k)) :
    oldNestedMixedBraidMap D (parameterTwist D Sc) cutoff i j N =
      tripleDotCorrectionPolynomial D Sc
        (R := End (induced (append D (parameterTwist D Sc) cutoff i)
          (induced (append D (parameterTwist D Sc) cutoff j)
            (induced (append D (parameterTwist D Sc) cutoff i) N)))) i j
        ((induction (append D (parameterTwist D Sc) cutoff i)).map
          ((induction (append D (parameterTwist D Sc) cutoff j)).map
            (dotEnd (append D (parameterTwist D Sc) cutoff i)
              (oldAppendDot_supernatural D (parameterTwist D Sc) cutoff i) N)))
        ((induction (append D (parameterTwist D Sc) cutoff i)).map
          (dotEnd (append D (parameterTwist D Sc) cutoff j)
            (oldAppendDot_supernatural D (parameterTwist D Sc) cutoff j)
            ((induction (append D (parameterTwist D Sc) cutoff i)).obj N)))
        (dotEnd (append D (parameterTwist D Sc) cutoff i)
          (oldAppendDot_supernatural D (parameterTwist D Sc) cutoff i)
          ((induction (append D (parameterTwist D Sc) cutoff j)).obj
            ((induction (append D (parameterTwist D Sc) cutoff i)).obj N))) := by
  let J := append D (parameterTwist D Sc) cutoff i
  let K := append D (parameterTwist D Sc) cutoff j
  let e := inductionTripleFlattening J K J N
  have hp := inductionTripleFlattening_polynomial D Sc i j J K J
    (oldAppendDot_supernatural D (parameterTwist D Sc) cutoff i)
    (oldAppendDot_supernatural D (parameterTwist D Sc) cutoff j)
    (oldAppendDot_supernatural D (parameterTwist D Sc) cutoff i) hij N
  have hc := transformComponent_congr_pointwise ((J ⋙ K) ⋙ J)
    (tripleSourcePolynomial_supernatural ((J ⋙ K) ⋙ J) D (parameterTwist D Sc) i j
      (((oldAppendDot_supernatural D (parameterTwist D Sc) cutoff i).whiskerRight K).whiskerRight J)
      (((oldAppendDot_supernatural D (parameterTwist D Sc) cutoff j).whiskerLeft J).whiskerRight J)
      ((oldAppendDot_supernatural D (parameterTwist D Sc) cutoff i).whiskerLeft (J ⋙ K)) hij)
    (tripleCorrection_supernatural D (parameterTwist D Sc) cutoff hij)
    (fun s => (tripleCorrection_tripleDots D (parameterTwist D Sc) cutoff i j s).symm) N
  have hh := congrArg (fun f => inductionEndConjugation (k := k) e
    (sign k (D.parity i * D.parity j) • f)) hc
  rw [oldNestedMixedBraidMap_conjugate, oldDirectMixedBraidMap_coefficient D Sc cutoff hij N]
  exact hh.symm.trans hp.symm

/-- The nested braid difference retains the selected negative equal and positive distinct crossings. -/
theorem oldNestedMixedBraidMap_normalized {i j : I} (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    oldNestedMixedBraidMap D Sc cutoff i j N =
      (show End ((induction (A i)).obj ((induction (A j)).obj ((induction (A i)).obj N))) from
        normalizedNestedSuffix D Sc cutoff i j i N ≫ normalizedNestedPrefix D Sc cutoff i i j N ≫
          normalizedNestedSuffix D Sc cutoff i i j N) -
      (show End ((induction (A i)).obj ((induction (A j)).obj ((induction (A i)).obj N))) from
        normalizedNestedPrefix D Sc cutoff i j i N ≫ normalizedNestedSuffix D Sc cutoff j i i N ≫
          normalizedNestedPrefix D Sc cutoff j i i N) := by
  simp only [oldNestedMixedBraidMap, normalizedNestedPrefix, normalizedNestedSuffix,
    ite_true, ite_eq_right hij, ite_eq_right hij.symm, neg_one_smul, one_smul]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
