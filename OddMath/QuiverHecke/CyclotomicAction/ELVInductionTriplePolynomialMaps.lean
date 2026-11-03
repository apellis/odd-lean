/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionTripleCorrection
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionTripleDots
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionPairPolynomialMaps

/-! # The whole original-parameter correction through the triple chart

Brundan–Ellis (1.9): the polynomial in the three independent nested
induction dots is the same original-Sc correction through the prescribed
triple flattening. The source correction and its naturality are constructed
from the dots and parameter support, without comparison premises.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem triple_transform_total {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ)
    (N : Superfunctor k C (SVec k)) (w : E) :
    (transformComponent hγ N).total w = transformLinear hγ N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)
  (hc : IsSupernatural k (D.parity i) c)

/-- The entire module correction is the original-Sc ordered polynomial. -/
theorem transformComponent_triplePolynomial (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) :
    tripleDotCorrectionPolynomial D Sc (R := End (induced F N)) i j
        (transformComponent ha N) (transformComponent hb N) (transformComponent hc N) =
      sign k (D.parity i * D.parity j) •
        transformComponent (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc)
          i j ha hb hc hij) N := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  let ev : End (induced F N) →ₐ[k] Module.End k ((induced F N).obj w) :=
    (svecEndEvaluation ((induced F N).obj w)).comp (supernaturalEndEvaluation (induced F N) w)
  change ev (tripleDotCorrectionPolynomial D Sc i j
      (transformComponent ha N) (transformComponent hb N) (transformComponent hc N)) =
    ev (sign k (D.parity i * D.parity j) • transformComponent
      (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc) i j ha hb hc hij) N)
  rw [tripleDotCorrectionPolynomial_map, map_smul]
  change tripleDotCorrectionPolynomial D Sc (R := Module.End k ((induced F N).obj w)) i j
      ((transformComponent ha N).total w) ((transformComponent hb N).total w)
      ((transformComponent hc N).total w) =
    sign k (D.parity i * D.parity j) •
      ((transformComponent (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc)
        i j ha hb hc hij) N).total w)
  rw [triple_transform_total, triple_transform_total, triple_transform_total, triple_transform_total]
  exact transformLinear_triplePolynomial_eq F D Sc i j ha hb hc hij N w

section Chart
variable {A B : Type u}
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  {α : ∀ s, End (J.obj s)} {β : ∀ s, End (K.obj s)} {γ : ∀ s, End (L.obj s)}
  (hα : IsSupernatural k (D.parity i) α) (hβ : IsSupernatural k (D.parity j) β)
  (hγ : IsSupernatural k (D.parity i) γ)

/-- The actual three nested dots give the same correction under the chosen triple chart. -/
theorem inductionTripleFlattening_polynomial (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) :
    tripleDotCorrectionPolynomial D Sc (R := End (induced L (induced K (induced J N)))) i j
        ((induction L).map ((induction K).map (dotEnd J hα N)))
        ((induction L).map (dotEnd K hβ ((induction J).obj N)))
        (dotEnd L hγ ((induction K).obj ((induction J).obj N))) =
      inductionEndConjugation (k := k) (inductionTripleFlattening J K L N)
        (sign k (D.parity i * D.parity j) • transformComponent
          (tripleSourcePolynomial_supernatural ((J ⋙ K) ⋙ L) D (parameterTwist D Sc) i j
            ((hα.whiskerRight K).whiskerRight L) ((hβ.whiskerLeft J).whiskerRight L)
            (hγ.whiskerLeft (J ⋙ K)) hij) N) := by
  let e := inductionTripleFlattening J K L N
  have ht := transformComponent_triplePolynomial ((J ⋙ K) ⋙ L) D Sc i j
    ((hα.whiskerRight K).whiskerRight L) ((hβ.whiskerLeft J).whiskerRight L)
    (hγ.whiskerLeft (J ⋙ K)) hij N
  have hp := congrArg (fun z : End (induced ((J ⋙ K) ⋙ L) N) =>
    inductionEndConjugation (k := k) e z) ht
  rw [tripleDotCorrectionPolynomial_map] at hp
  have h₁ : inductionEndConjugation (k := k) e
      (transformComponent ((hα.whiskerRight K).whiskerRight L) N) =
      (induction L).map ((induction K).map (dotEnd J hα N)) :=
    inductionEndConjugation_of_square e _ _ (inductionTripleFlattening_first_dot J K L hα N)
  have h₂ : inductionEndConjugation (k := k) e
      (transformComponent ((hβ.whiskerLeft J).whiskerRight L) N) =
      (induction L).map (dotEnd K hβ ((induction J).obj N)) :=
    inductionEndConjugation_of_square e _ _ (inductionTripleFlattening_middle_dot J K L hβ N)
  have h₃ : inductionEndConjugation (k := k) e
      (transformComponent (hγ.whiskerLeft (J ⋙ K)) N) =
      dotEnd L hγ ((induction K).obj ((induction J).obj N)) :=
    inductionEndConjugation_of_square e _ _ (inductionTripleFlattening_last_dot J K L hγ N)
  rw [h₁, h₂, h₃] at hp
  exact hp
end Chart
end OddMath.QuiverHecke.ELVOld.BalancedInduction
