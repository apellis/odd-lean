/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPInduction

/-!
# The relation-killing step (K) with a right context

`DeformedGlobalQP.md`, §2: after the strand of colour `i` has crossed the prefix
`μ ++ [i]` and the last old `i` has been brought back to the front, the first-position
relation `f_i(x₁)` lies in the old cyclotomic ideal. This file proves the version with an
arbitrary right context `σ`, which the all-prefix induction needs:

* `killE_whiskerLeft_comp`: precomposition by `1_i ⊗ g` kills when `g` lies in the old
  cyclotomic kernel;
* `killE_relation_context`: the identity (K) on the word `i :: (μ ++ [i] ++ σ)`.

Supporting whiskering identities: `twist_whiskerRight_obj` (the parity twist commutes with
right whiskering), `whiskerLeft_whiskerRight_cons`, `whiskerRight_whiskerRight_word`
(associativity of whiskering by words) and `whiskerLeft_dotE_cons`.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

section Whisker

/-- The parity twist commutes with right whiskering. -/
theorem twist_whiskerRight_obj (p : ZMod 2) {A B : (pres D Sc).Presented} (f : A ⟶ B)
    (Z : (pres D Sc).Presented) :
    Supercategory.twist k p (f ▷ Z) = Supercategory.twist k p f ▷ Z := by
  refine Supercategory.induction_on (R := k) f ?_ (fun q g hg => ?_) (fun g h hg hh => ?_)
  · rw [map_zero, MonoidalSupercategory.zero_whiskerRight k Z, map_zero]
  · rw [Supercategory.twist_of_mem p hg,
      Supercategory.twist_of_mem p (MonoidalSupercategory.whiskerRight_mem (R := k) Z hg),
      MonoidalSupercategory.smul_whiskerRight (R := k)]
  · rw [MonoidalSupercategory.add_whiskerRight (R := k), map_add, map_add, hg, hh,
      MonoidalSupercategory.add_whiskerRight (R := k)]

/-- Right whiskering of a left whiskering by a letter, on words. -/
theorem whiskerLeft_whiskerRight_cons (i : I) {t t' : List I}
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) (σ : List I) :
    ((pres D Sc).obj (ob D [i]) ◁ g) ▷ (pres D Sc).obj (ob D σ) =
      ((pres D Sc).obj (ob D [i]) ◁ (g ▷ (pres D Sc).obj (ob D σ)) :
        (pres D Sc).obj (ob D (i :: (t ++ σ))) ⟶ (pres D Sc).obj (ob D (i :: (t' ++ σ)))) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D [i]))) g (𝟙 ((pres D Sc).obj (ob D σ)))
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  simpa using h

/-- Right whiskering by two words is right whiskering by their concatenation. -/
theorem whiskerRight_whiskerRight_word {w w' : List I}
    (f : (pres D Sc).obj (ob D w) ⟶ (pres D Sc).obj (ob D w')) (s t : List I) :
    (f ▷ (pres D Sc).obj (ob D s)) ▷ (pres D Sc).obj (ob D t) =
      eqToHom (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc w s t)) ≫
        (f ▷ (pres D Sc).obj (ob D (s ++ t))) ≫
          eqToHom (congrArg (fun x => (pres D Sc).obj (ob D x))
            (List.append_assoc w' s t).symm) := by
  have h := MonoidalSupercategory.associator_naturality (R := k) f
    (𝟙 ((pres D Sc).obj (ob D s))) (𝟙 ((pres D Sc).obj (ob D t)))
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  rw [comp_eqToHom_iff] at h
  rw [h, Category.assoc]
  rfl

/-- Left whiskering a dot by a letter shifts its position. -/
theorem whiskerLeft_dotE_cons (i : I) (w : List I) (b : ℕ) :
    (pres D Sc).obj (ob D [i]) ◁ dotE D Sc w b = dotE D Sc (i :: w) (b + 1) := by
  rw [dotE_eq, cl_whiskerLeft, dotE_eq]
  exact cl_congr_gs D Sc (by simp [PG.shift]; omega) _ _

/-- Right whiskering by a word, as a homomorphism of `k`-algebras. -/
def whiskerWordAlgHom (w s : List I) :
    End ((pres D Sc).obj (ob D w)) →ₐ[k] End ((pres D Sc).obj (ob D (w ++ s))) where
  __ := whiskerWordRingHom D Sc w s
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change (c • 𝟙 _) ▷ _ = c • 𝟙 _
    rw [MonoidalSupercategory.smul_whiskerRight (R := k),
      MonoidalSupercategory.id_whiskerRight (R := k)]
    rfl

@[simp] theorem whiskerWordAlgHom_apply (w s : List I) (f : End ((pres D Sc).obj (ob D w))) :
    whiskerWordAlgHom D Sc w s f = f ▷ (pres D Sc).obj (ob D s) := rfl

/-- A polynomial in the first dot keeps its meaning after right whiskering. -/
theorem aeval_dotE_whiskerRight (w s : List I) (hw : 0 < w.length) (q : _root_.Polynomial k) :
    _root_.Polynomial.aeval (dotE D Sc w 0) q ▷ (pres D Sc).obj (ob D s) =
      _root_.Polynomial.aeval (dotE D Sc (w ++ s) 0) q := by
  rw [← whiskerWordAlgHom_apply, ← _root_.Polynomial.aeval_algHom_apply, whiskerWordAlgHom_apply,
    dotE_whiskerRight D Sc w s 0 hw]

end Whisker

variable [Fintype I] (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

section Killing

/-- Precomposition by `1_i ⊗ g` kills as soon as the old matrix of `g` lies in the old
cyclotomic kernel. -/
theorem killE_whiskerLeft_comp {W t : Word I (n + 1)} (g : wordObj D Sc W ⟶ wordObj D Sc t)
    (Y : wordObj D Sc (prependWord i t) ⟶ wordObj D Sc (prependWord i W))
    (hg : cyclotomicMk D Sc a n (FiniteHomMatrix.single t W g) = 0) :
    KillE D Sc i β a ha n W
      (((pres D Sc).obj (ob D [i]) ◁ g : wordObj D Sc (prependWord i W) ⟶
        wordObj D Sc (prependWord i t)) ≫ Y) := by
  unfold KillE
  change PrependKills D Sc i β a ha n
    (FiniteHomMatrix.single (prependWord i W) (prependWord i W)
      (prependHom D Sc i W t g ≫ Y))
  rw [← FiniteHomMatrix.single_mul_single, ← prependLinear_single]
  exact PrependKills.mul_left (prependKills_of_cyclotomicMk hg) _

/-- (K) with a right context `σ`: after the strand of colour `i` crosses `μ ++ [i]` and the
last old `i` is brought to the front, the first-position relation `f_i(x₁)` kills, on the
word `i :: (μ ++ [i] ++ σ)`. -/
theorem killE_relation_context (μ σ : List I) (hW : (μ ++ [i] ++ σ).length = n + 1) :
    KillE D Sc i β a ha n ⟨μ ++ [i] ++ σ, hW⟩
      (((moveHom D Sc i [] (μ ++ [i]) ≫
          (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) ▷
            (pres D Sc).obj (ob D σ) :
          End ((pres D Sc).obj (ob D (i :: (μ ++ [i] ++ σ))))) ≫
        _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i] ++ σ)) 0) (a i)) := by
  set p := D.parity i * wordSumParity D (μ ++ [i])
  set Fμ := _root_.Polynomial.aeval (dotE D Sc (i :: μ) 0) (a i)
  set h : (pres D Sc).obj (ob D (μ ++ [i])) ⟶ (pres D Sc).obj (ob D (i :: μ)) :=
    lastToFirstHom D Sc i μ ≫ Fμ
  have hF1 : _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i])) 0) (a i) =
      Fμ ▷ (pres D Sc).obj (ob D [i]) :=
    (aeval_dotE_whiskerRight D Sc (i :: μ) [i] (by simp) _).symm
  have hF2 : _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i] ++ σ)) 0) (a i) =
      _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i])) 0) (a i) ▷
        (pres D Sc).obj (ob D σ) :=
    (aeval_dotE_whiskerRight D Sc (i :: (μ ++ [i])) σ (by simp) _).symm
  have hA : moveHom D Sc i [] (μ ++ [i]) ≫ (h ▷ (pres D Sc).obj (ob D [i])) =
      ((pres D Sc).obj (ob D [i]) ◁ Supercategory.twist k p h) ≫
        moveHom D Sc i [] (i :: μ) := by
    rw [hom_comp_moveHom D Sc i (Supercategory.twist k p h), Supercategory.twist_twist]
  have hB : (moveHom D Sc i [] (μ ++ [i]) ≫
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) ≫
        _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i])) 0) (a i) =
      moveHom D Sc i [] (μ ++ [i]) ≫ (h ▷ (pres D Sc).obj (ob D [i])) := by
    rw [hF1, Category.assoc, ← MonoidalSupercategory.comp_whiskerRight (R := k)]
  have hC : (((moveHom D Sc i [] (μ ++ [i]) ≫
          (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) ▷
            (pres D Sc).obj (ob D σ) :
          End ((pres D Sc).obj (ob D (i :: (μ ++ [i] ++ σ))))) ≫
        _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i] ++ σ)) 0) (a i)) =
      ((pres D Sc).obj (ob D [i]) ◁
          (Supercategory.twist k p h ▷ (pres D Sc).obj (ob D σ))) ≫
        (moveHom D Sc i [] (i :: μ) ▷ (pres D Sc).obj (ob D σ)) := by
    rw [hF2, ← MonoidalSupercategory.comp_whiskerRight (R := k), hB, hA,
      MonoidalSupercategory.comp_whiskerRight (R := k), whiskerLeft_whiskerRight_cons]
  rw [hC]
  have ht : (i :: μ ++ σ).length = n + 1 := by simp at hW ⊢; omega
  refine killE_whiskerLeft_comp D Sc i β a ha n (t := ⟨i :: μ ++ σ, ht⟩) _ _ ?_
  rw [← twist_whiskerRight_obj, MonoidalSupercategory.comp_whiskerRight (R := k),
    aeval_dotE_whiskerRight D Sc (i :: μ) σ (by simp)]
  have hg := cyclotomicMk_twist_relation D Sc a ha n p ⟨i :: μ ++ σ, ht⟩ 1
    (FiniteHomMatrix.single (⟨i :: μ ++ σ, ht⟩ : Word I (n + 1)) ⟨μ ++ [i] ++ σ, hW⟩
      (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D σ)))
  rw [one_mul, cyclotomicGenerator, FiniteHomMatrix.single_mul_single,
    homMatrixTwist_single] at hg
  exact hg

end Killing

end OddMath.QuiverHecke
