/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputOrderBalance
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveExtraction

/-!
# Leading-source monomials for the output boundary

Hom-level source-dot separation for the ordered-product comparison in
`DeformedMackeyBoundary.md` (2), without a finite colour-type assumption.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory Supercategory
open scoped TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
local notation "O[" w "]" => Presentation.obj (pres D Sc) (ob D w)

private theorem source_dot_cons (w : List I) (p : ℕ) (ps : List ℕ) :
    endpointDotMonomial D Sc w (p :: ps) =
      dotE D Sc w p ≫ endpointDotMonomial D Sc w ps := by
  rw [dotE_eq_cl D Sc (sChain_dotAny w p)]
  unfold endpointDotMonomial
  rw [cl_comp]
  rfl

private theorem left_dot_interchange {A B : (pres D Sc).Presented}
    {q : ZMod 2} {x : End A} (hx : x ∈ parity (R := k) A A q) (f : End B) :
    x ▷ B ≫ A ◁ f = A ◁ twist k q f ≫ x ▷ B := by
  refine Supercategory.induction_on (R := k) f ?_ (fun r g hg => ?_)
    (fun f g hf hg => ?_)
  · simp only [map_zero, MonoidalSupercategory.whiskerLeft_zero (R := k),
      Limits.comp_zero, Limits.zero_comp]
  · rw [twist_of_mem _ hg, MonoidalSupercategory.whiskerLeft_smul (R := k),
      Linear.smul_comp, MonoidalSupercategory.super_interchange hx hg,
      koszulSign_smul (R := k)]
  · simp only [map_add, MonoidalSupercategory.whiskerLeft_add (R := k),
      Preadditive.comp_add, Preadditive.add_comp, hf, hg]

private theorem first_dot_old (i : I) (v : List I) (f : End O[v]) :
    dotE D Sc (i :: v) 0 ≫ O[[i]] ◁ f =
      O[[i]] ◁ twist k (D.parity i) f ≫ dotE D Sc (i :: v) 0 := by
  have hd : dotE D Sc (i :: v) 0 = (inductionStrandDot D Sc i ▷ O[v]) :=
    (inductionFirstDot_eq_dotE D Sc i ⟨v, rfl⟩).symm
  rw [hd]
  exact left_dot_interchange D Sc (inductionStrandDot_parity D Sc i) f

/-- Hom-valued source separation, with the source-category object family fixed. -/
def separatedSourceOldHom (i : I) (v : List I) : List ℕ → End O[v]
  | [] => 𝟙 _
  | 0 :: ps => twist k (D.parity i) (separatedSourceOldHom i v ps)
  | (p + 1) :: ps => dotE D Sc v p ≫ separatedSourceOldHom i v ps

/-- Exact Hom separation of source dots, retaining every old parity twist. -/
theorem endpointDotMonomial_separate_hom (i : I) (v : List I) (ps : List ℕ) :
    endpointDotMonomial D Sc (i :: v) ps =
      O[[i]] ◁ separatedSourceOldHom D Sc i v ps ≫
        dotE D Sc (i :: v) 0 ^ sourceMovingDegree ps := by
  induction ps with
  | nil =>
    simp only [separatedSourceOldHom, sourceMovingDegree, pow_zero, End.one_def,
      MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp]
    exact cl_nil D Sc (i :: v) rfl
  | cons p ps ih =>
    rw [source_dot_cons, ih]
    cases p with
    | zero =>
      rw [← Category.assoc, first_dot_old, Category.assoc]
      simp only [separatedSourceOldHom, sourceMovingDegree, pow_succ, End.mul_def]
    | succ p =>
      rw [← whiskerLeft_letter_dotE D Sc i v p, ← Category.assoc]
      simp only [separatedSourceOldHom, sourceMovingDegree,
        MonoidalSupercategory.whiskerLeft_comp (R := k)]

/-- Separation signs cancel on the independently specified square-product terms. -/
theorem separatedSourceOldHom_leading (i : I) (v μ : List I) (a : ℕ)
    (c : MoveChoices μ) :
    separatedSourceOldHom D Sc i v (leadingSourceDots D i 0 a μ c) =
      endpointDotMonomial D Sc v (sourceOldDots (leadingSourceDots D i 0 a μ c)) := by
  induction μ generalizing a with
  | nil => exact (cl_nil D Sc v rfl).symm
  | cons j μ ih =>
    rcases c with ⟨b, c⟩
    by_cases hij : i = j
    · subst j
      rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
      all_goals
        fin_cases b <;>
          simp [leadingSourceDots, leadingSourceBlockDots, hi, sourceOldDots,
            separatedSourceOldHom, source_dot_cons, twist_twist, ih]
    · simp [leadingSourceDots, leadingSourceBlockDots, hij, ih]

/-- A leading source monomial has its independently computed old dot factor. -/
theorem leadingSourceDots_separate_hom (i : I) (v : List I) (c : MoveChoices v) :
    endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c) =
      O[[i]] ◁ endpointDotMonomial D Sc v
        (sourceOldDots (leadingSourceDots D i 0 0 v c)) ≫
      dotE D Sc (i :: v) 0 ^ sourceMovingDegree (leadingSourceDots D i 0 0 v c) := by
  rw [endpointDotMonomial_separate_hom, separatedSourceOldHom_leading]

namespace ELVOld
variable (cutoff : I → ℕ)

/-- The old affine dot monomial specified by a choice in the ordered product. -/
def leadingSourceOldArrow (i : I) (v : List I) (c : MoveChoices v) : hom D Sc cutoff v v :=
  affineUnit D Sc cutoff v v
    (endpointDotMonomial D Sc v (sourceOldDots (leadingSourceDots D i 0 0 v c)))

/-- Every old twist fixes the independent old dot monomial, also in full ELV. -/
theorem leadingSourceOldArrow_twist (i : I) (v : List I) (c : MoveChoices v) (q : ZMod 2) :
    twist k q (leadingSourceOldArrow D Sc cutoff i v c) =
      leadingSourceOldArrow D Sc cutoff i v c := by
  unfold leadingSourceOldArrow
  rw [← affineUnit_twist]
  congr 1
  exact leadingMoveOldDots_twist D Sc i v c q

private theorem leading_degree_sign (i : I) (v : List I) (c : MoveChoices v) (q : ZMod 2) :
    (SKM.zsign k (D.parity i * q)) ^
      sourceMovingDegree (leadingSourceDots D i 0 0 v c) = 1 := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · simp [hi, SKM.zsign]
  · have he := sourceMovingDegree_leadingSourceDots_even D i hi 0 v c
    have hd : Even (sourceMovingDegree (leadingSourceDots D i 0 0 v c)) :=
      Nat.even_iff.mpr he
    unfold SKM.zsign
    split_ifs
    · exact hd.neg_one_pow
    · simp

private theorem leading_source_pair (p : ZMod 2) (i : I) (v : List I) (c : MoveChoices v) :
    projection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff (i :: v) (v ++ [i])
        (endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c) ≫
          OutputOldComposite.bareU D Sc i v)) =
    pair D Sc cutoff p i
      (movingPower D Sc cutoff i v (sourceMovingDegree (leadingSourceDots D i 0 0 v c)) ≫
        bareUFull D Sc cutoff i v)
      ((ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)) := by
  rw [pair_mk, leadingSourceOldArrow_twist, leadingSourceDots_separate_hom,
    Category.assoc]
  congr 1
  rw [leadingSourceOldArrow, insert_affineUnit]
  change affineUnit D Sc cutoff _ _ (_ ≫ (_ ≫ _)) =
    affineUnit D Sc cutoff _ _ _ ≫
      (affineUnit D Sc cutoff _ _ _ ≫ affineUnit D Sc cutoff _ _ _)
  rw [affineUnit_comp, affineUnit_comp]
  rfl

/-- Input-to-output transport of an independent leading source monomial, modulo
exact chronological short span, not total crossing length. -/
theorem leading_source_output_transport (i : I) (v : List I) (c : MoveChoices v) :
    projection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff (i :: v) (v ++ [i])
        (endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c) ≫
          OutputOldComposite.bareU D Sc i v) -
        ((bareUFull D Sc cutoff i v ≫
          appendInsert D Sc cutoff i v v (leadingSourceOldArrow D Sc cutoff i v c)) ≫
          appendMovingPower D Sc cutoff i v
            (sourceMovingDegree (leadingSourceDots D i 0 0 v c)))) ∈
      chronologicalShortSpan D Sc cutoff i v v := by
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff 0 i v]
  change outputLongExtraction D Sc cutoff 0 i v _ = 0
  rw [map_sub, map_sub, sub_eq_zero]
  ext n
  rw [outputLongExtraction_apply, outputLongExtraction_apply, leading_source_pair,
    coordinate_long_row, leading_degree_sign]
  rw [← pair_id D Sc cutoff 0 i,
    canonical_output_monomial D Sc cutoff 0 i v _ n _ _ _ rfl]
  split_ifs
  · rw [one_smul]
    change (ideal D Sc cutoff v v).mkQ _ =
      (ideal D Sc cutoff v v).mkQ (𝟙 _ ≫ twist k _ _)
    rw [Category.id_comp, leadingSourceOldArrow_twist]
  · rfl

/-- The canonical output extractor evaluates each independently specified
leading-source monomial. No transport premise is assumed. -/
theorem leading_source_output_extraction (p : ZMod 2) (i : I) (v : List I)
    (c : MoveChoices v) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          (endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c) ≫
            OutputOldComposite.bareU D Sc i v))) =
      Finsupp.single (sourceMovingDegree (leadingSourceDots D i 0 0 v c))
        ((ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)) := by
  have ht := leading_source_output_transport D Sc cutoff i v c
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v] at ht
  change outputLongExtraction D Sc cutoff p i v _ = 0 at ht
  rw [map_sub, map_sub, sub_eq_zero] at ht
  rw [ht, ← pair_id D Sc cutoff p i, canonical_output_extraction D Sc cutoff p i v _ _ _ _ rfl]
  congr 1
  change (ideal D Sc cutoff v v).mkQ (𝟙 _ ≫ twist k _ _) = _
  rw [Category.id_comp, leadingSourceOldArrow_twist]

end ELVOld
end OddMath.QuiverHecke
