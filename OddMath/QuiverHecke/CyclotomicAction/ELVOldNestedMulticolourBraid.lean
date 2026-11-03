/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularTriple
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMulticolourInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleMate

/-! # The uncorrected OLD braid on nested triple induction

Brundan–Ellis (1.9): the actual independent pair crossings satisfy the
whole nested balanced-induction braid. The six prescribed triple
flattening squares compare them to the proved coefficient braid.
The final uncorrected theorem retains negative equal and positive distinct
pair crossings. The repeated-outer correction remains a separate attachment.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction
universe u

private theorem compose_three_squares {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C}
    (e₀ : X₀ ⟶ Y₀) (e₁ : X₁ ⟶ Y₁) (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃)
    (a₀ : X₀ ⟶ X₁) (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₀ : Y₀ ⟶ Y₁) (b₁ : Y₁ ⟶ Y₂) (b₂ : Y₂ ⟶ Y₃)
    (h₀ : a₀ ≫ e₁ = e₀ ≫ b₀) (h₁ : a₁ ≫ e₂ = e₁ ≫ b₁)
    (h₂ : a₂ ≫ e₃ = e₂ ≫ b₂) :
    (a₀ ≫ a₁ ≫ a₂) ≫ e₃ = e₀ ≫ (b₀ ≫ b₁ ≫ b₂) := by
  simp only [Category.assoc]
  rw [h₂, ← Category.assoc a₁, h₁,
    Category.assoc e₁, ← Category.assoc a₀, h₀, Category.assoc]

private theorem transform_degree_congr
    {k C B : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p q : ZMod 2} (hp : p = q) {γ : ∀ s, F.obj s ⟶ G.obj s}
    (hγ : IsSupernatural k p γ) (hδ : IsSupernatural k q γ)
    (M : Superfunctor k C (SVec k)) : transformComponent hγ M = transformComponent hδ M := by
  cases hp
  rfl

private theorem scaled_three_paths
    {k : Type u} [CommRing k] {C : Type*} [Category* C] [Preadditive C] [Linear k C]
    {X₀ X₁ X₂ X₃ X₄ X₅ : C} (a b c : k)
    (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₀ : X₀ ⟶ X₄) (g₁ : X₄ ⟶ X₅) (g₂ : X₅ ⟶ X₃)
    (hb : f₀ ≫ f₁ ≫ f₂ = g₀ ≫ g₁ ≫ g₂) :
    (a • f₀) ≫ (b • f₁) ≫ (c • f₂) = (c • g₀) ≫ (b • g₁) ≫ (a • g₂) := by
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
  rw [hb]
  congr 1
  ring

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local notation "A" i => append D Sc cutoff i

/-- The independently chosen positive first pair crossing, induced by the third append. -/
abbrev nestedPrefix (i j l : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  (induction (A l)).map
    (mixedCrossComponent (A i) (A j) (Distinct.cross_supernatural D Sc cutoff i j) M)

/-- The independently chosen positive last pair crossing after the first induction. -/
abbrev nestedSuffix (i j l : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  mixedCrossComponent (A j) (A l) (Distinct.cross_supernatural D Sc cutoff j l)
    ((induction (A i)).obj M)

theorem nestedPrefix_flatten (i j l : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    nestedPrefix D Sc cutoff i j l M ≫ (inductionTripleFlattening (A j) (A i) (A l) M).hom =
      (inductionTripleFlattening (A i) (A j) (A l) M).hom ≫ transformComponent (triplePrefix_supernatural D Sc cutoff j i l) M := by
  have ht := inductionTripleFlattening_prefix_rectangular (A i) (A j) (A j) (A i) (A l)
    (Distinct.cross_supernatural D Sc cutoff i j) M
  have he := transform_degree_congr (mul_comm (D.parity i) (D.parity j))
    ((Distinct.cross_supernatural D Sc cutoff i j).whiskerRight (A l))
    (triplePrefix_supernatural D Sc cutoff j i l) M
  exact ht.trans (congrArg (fun f => (inductionTripleFlattening (A i) (A j) (A l) M).hom ≫ f) he)

theorem nestedSuffix_flatten (i j l : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    nestedSuffix D Sc cutoff i j l M ≫ (inductionTripleFlattening (A i) (A l) (A j) M).hom =
      (inductionTripleFlattening (A i) (A j) (A l) M).hom ≫ transformComponent (tripleSuffix_supernatural D Sc cutoff i l j) M := by
  have ht := inductionTripleFlattening_suffix_rectangular (A i) (A j) (A l) (A l) (A j)
    (Distinct.cross_supernatural D Sc cutoff j l) M
  have he := transform_degree_congr (mul_comm (D.parity j) (D.parity l))
    ((Distinct.cross_supernatural D Sc cutoff j l).whiskerLeft (A i))
    (tripleSuffix_supernatural D Sc cutoff i l j) M
  exact ht.trans (congrArg (fun f => (inductionTripleFlattening (A i) (A j) (A l) M).hom ≫ f) he)

/-- The actual positive nested pair crossings satisfy the entire uncorrected braid. -/
theorem nestedTripleCross_braid (i j l : I) (hb : ¬ (i = l ∧ i ≠ j))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    nestedPrefix D Sc cutoff l j i M ≫ nestedSuffix D Sc cutoff j l i M ≫
        nestedPrefix D Sc cutoff j i l M =
      nestedSuffix D Sc cutoff l j i M ≫ nestedPrefix D Sc cutoff l i j M ≫
        nestedSuffix D Sc cutoff i l j M := by
  apply (cancel_mono (inductionTripleFlattening (A i) (A j) (A l) M).hom).mp
  have hL := compose_three_squares
    (inductionTripleFlattening (A l) (A j) (A i) M).hom (inductionTripleFlattening (A j) (A l) (A i) M).hom (inductionTripleFlattening (A j) (A i) (A l) M).hom (inductionTripleFlattening (A i) (A j) (A l) M).hom
    (nestedPrefix D Sc cutoff l j i M) (nestedSuffix D Sc cutoff j l i M)
    (nestedPrefix D Sc cutoff j i l M)
    (transformComponent (triplePrefix_supernatural D Sc cutoff j l i) M)
    (transformComponent (tripleSuffix_supernatural D Sc cutoff j i l) M)
    (transformComponent (triplePrefix_supernatural D Sc cutoff i j l) M)
    (nestedPrefix_flatten D Sc cutoff l j i M) (nestedSuffix_flatten D Sc cutoff j l i M)
    (nestedPrefix_flatten D Sc cutoff j i l M)
  have hR := compose_three_squares
    (inductionTripleFlattening (A l) (A j) (A i) M).hom (inductionTripleFlattening (A l) (A i) (A j) M).hom (inductionTripleFlattening (A i) (A l) (A j) M).hom (inductionTripleFlattening (A i) (A j) (A l) M).hom
    (nestedSuffix D Sc cutoff l j i M) (nestedPrefix D Sc cutoff l i j M)
    (nestedSuffix D Sc cutoff i l j M)
    (transformComponent (tripleSuffix_supernatural D Sc cutoff l i j) M)
    (transformComponent (triplePrefix_supernatural D Sc cutoff i l j) M)
    (transformComponent (tripleSuffix_supernatural D Sc cutoff i j l) M)
    (nestedSuffix_flatten D Sc cutoff l j i M) (nestedPrefix_flatten D Sc cutoff l i j M)
    (nestedSuffix_flatten D Sc cutoff i l j M)
  exact hL.trans ((congrArg (fun f => (inductionTripleFlattening (A l) (A j) (A i) M).hom ≫ f)
    (directTripleCross_braid D Sc cutoff i j l hb M)).trans hR.symm)

private theorem pairCross_equal (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    mixedCrossComponent (A i) (A i) (Distinct.cross_supernatural D Sc cutoff i i) M =
      equalCrossOnDoubleInduction D Sc cutoff i M := rfl

/-- Normalization preserves the negative equal and positive distinct pair crossings. -/
abbrev normalizedNestedPrefix (i j l : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  (if i = j then (-1 : k) else 1) • nestedPrefix D Sc cutoff i j l M

/-- The independently normalized last-pair crossing after the first induction. -/
abbrev normalizedNestedSuffix (i j l : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  (if j = l then (-1 : k) else 1) • nestedSuffix D Sc cutoff i j l M

theorem normalizedNestedPrefix_equal (i l : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    normalizedNestedPrefix D Sc cutoff i i l M =
      -(induction (A l)).map (equalCrossOnDoubleInduction D Sc cutoff i M) := by
  simp only [normalizedNestedPrefix, ite_true, neg_one_smul]
  exact congrArg (fun f => -(induction (A l)).map f) (pairCross_equal D Sc cutoff i M)

theorem normalizedNestedSuffix_equal (i j : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    normalizedNestedSuffix D Sc cutoff i j j M =
      -equalCrossOnDoubleInduction D Sc cutoff j ((induction (A i)).obj M) := by
  simp only [normalizedNestedSuffix, ite_true, neg_one_smul]
  exact congrArg Neg.neg (pairCross_equal D Sc cutoff j ((induction (A i)).obj M))

theorem normalizedNestedPrefix_distinct (i j l : I) (hij : i ≠ j)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    normalizedNestedPrefix D Sc cutoff i j l M = nestedPrefix D Sc cutoff i j l M := by
  simp only [normalizedNestedPrefix, ite_eq_right hij, one_smul]

theorem normalizedNestedSuffix_distinct (i j l : I) (hjl : j ≠ l)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    normalizedNestedSuffix D Sc cutoff i j l M = nestedSuffix D Sc cutoff i j l M := by
  simp only [normalizedNestedSuffix, ite_eq_right hjl, one_smul]

/-- The negative equal and positive distinct nested crossings satisfy the uncorrected braid. -/
theorem normalizedNestedTripleCross_braid (i j l : I) (hb : ¬ (i = l ∧ i ≠ j))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    normalizedNestedPrefix D Sc cutoff l j i M ≫ normalizedNestedSuffix D Sc cutoff j l i M ≫
        normalizedNestedPrefix D Sc cutoff j i l M =
      normalizedNestedSuffix D Sc cutoff l j i M ≫ normalizedNestedPrefix D Sc cutoff l i j M ≫
        normalizedNestedSuffix D Sc cutoff i l j M := by
  exact scaled_three_paths
    (if l = j then (-1 : k) else 1) (if l = i then (-1 : k) else 1)
    (if j = i then (-1 : k) else 1)
    (nestedPrefix D Sc cutoff l j i M) (nestedSuffix D Sc cutoff j l i M)
    (nestedPrefix D Sc cutoff j i l M) (nestedSuffix D Sc cutoff l j i M)
    (nestedPrefix D Sc cutoff l i j M) (nestedSuffix D Sc cutoff i l j M)
    (nestedTripleCross_braid D Sc cutoff i j l hb M)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
