/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleCorrectedBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularTriple

/-! # The corrected braid on a seven-edge induction grid

Brundan–Ellis (1.9): retain the seven different append edges in the three
repeated-outer orderings. The six independent rectangular/equal crossings
and three independent dots are compared through the chosen triple charts.
The generic intermediate takes the literal source coefficient equation;
concrete stored-target actions must discharge it from the OLD quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem grid_three_squares {C : Type*} [Category* C]
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

private theorem grid_negative_square {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (a : End X) (e : X ⟶ Y) (b : End Y)
    (h : a ≫ e = e ≫ b) : (-a) ≫ e = e ≫ (-b) := by
  rw [Preadditive.neg_comp, Preadditive.comp_neg, h]

private theorem grid_difference_square {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (a b : End X) (c d : End Y) (e : X ⟶ Y)
    (ha : a ≫ e = e ≫ c) (hb : b ≫ e = e ≫ d) :
    (a - b) ≫ e = e ≫ (c - d) := by
  rw [Preadditive.sub_comp, Preadditive.comp_sub, ha, hb]

variable {k C A B P Q E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} P] [Preadditive P] [Linear k P] [Supercategory k P]
  [Category.{u} Q] [Preadditive Q] [Linear k Q] [Supercategory k Q]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (U : A ⥤ P) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (V : A ⥤ Q) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
  (W : B ⥤ Q) [W.Additive] [W.Linear k] [IsSuperfunctor k W]
  (L : P ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (M : Q ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I)
  {σ : ∀ s, (J ⋙ V).obj s ⟶ (K ⋙ W).obj s}
  {σ' : ∀ s, (K ⋙ W).obj s ⟶ (J ⋙ V).obj s}
  {τ : ∀ s, (J ⋙ U).obj s ⟶ (J ⋙ U).obj s}
  {ρ : ∀ s, (V ⋙ M).obj s ⟶ (U ⋙ L).obj s}
  {ρ' : ∀ s, (U ⋙ L).obj s ⟶ (V ⋙ M).obj s}
  {ξ : ∀ s, (W ⋙ M).obj s ⟶ (W ⋙ M).obj s}
  (hσ : IsSupernatural k (D.parity i * D.parity j) σ)
  (hσ' : IsSupernatural k (D.parity j * D.parity i) σ')
  (hτ : IsSupernatural k (D.parity i * D.parity i) τ)
  (hρ : IsSupernatural k (D.parity j * D.parity i) ρ)
  (hρ' : IsSupernatural k (D.parity i * D.parity j) ρ')
  (hξ : IsSupernatural k (D.parity i * D.parity i) ξ)
local notation "F₀" => (J ⋙ V) ⋙ M
local notation "F₁" => (J ⋙ U) ⋙ L
local notation "F₂" => (K ⋙ W) ⋙ M

/-- The independent paths on all seven grid edges, with the equal crossing negative. -/
def gridMixedBraid (N : Superfunctor k C (SVec k)) :
    End (induced M (induced V (induced J N))) :=
  (show End (induced M (induced V (induced J N))) from
    rectangularCrossComponent U V L M hρ' ((induction J).obj N) ≫
      (-(induction L).map (gridDoubleCrossComponent J U hτ N)) ≫
        rectangularCrossComponent V U M L hρ ((induction J).obj N)) -
  (show End (induced M (induced V (induced J N))) from
    (induction M).map (rectangularCrossComponent K J W V hσ' N) ≫
      (-gridDoubleCrossComponent W M hξ ((induction K).obj N)) ≫
        (induction M).map (rectangularCrossComponent J K V W hσ N))

/-- The direct three-functor source paths for this same grid. -/
def gridDirectMixedBraid (N : Superfunctor k C (SVec k)) : End (induced F₀ N) :=
  (show End (induced F₀ N) from
    transformComponent (hρ'.whiskerLeft J) N ≫
      (-transformComponent (hτ.whiskerRight L) N) ≫ transformComponent (hρ.whiskerLeft J) N) -
  (show End (induced F₀ N) from
    transformComponent (hσ'.whiskerRight M) N ≫
      (-transformComponent (hξ.whiskerLeft K) N) ≫ transformComponent (hσ.whiskerRight M) N)

/-- The six rectangular squares use the three prescribed triple charts. -/
theorem gridMixedBraid_conjugate (N : Superfunctor k C (SVec k)) :
    gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N =
      inductionEndConjugation (k := k) (inductionTripleFlattening J V M N)
        (gridDirectMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N) := by
  let e := inductionTripleFlattening J V M N
  let eR := inductionTripleFlattening J U L N
  let eL := inductionTripleFlattening K W M N
  have hR := grid_three_squares e.hom eR.hom eR.hom e.hom
    (rectangularCrossComponent U V L M hρ' ((induction J).obj N))
    (-(induction L).map (gridDoubleCrossComponent J U hτ N))
    (rectangularCrossComponent V U M L hρ ((induction J).obj N))
    (transformComponent (hρ'.whiskerLeft J) N) (-transformComponent (hτ.whiskerRight L) N)
    (transformComponent (hρ.whiskerLeft J) N)
    (inductionTripleFlattening_suffix_rectangular J V M U L hρ' N)
    (grid_negative_square _ _ _ (inductionTripleFlattening_prefix_rectangular J U J U L hτ N))
    (inductionTripleFlattening_suffix_rectangular J U L V M hρ N)
  have hL := grid_three_squares e.hom eL.hom eL.hom e.hom
    ((induction M).map (rectangularCrossComponent K J W V hσ' N))
    (-gridDoubleCrossComponent W M hξ ((induction K).obj N))
    ((induction M).map (rectangularCrossComponent J K V W hσ N))
    (transformComponent (hσ'.whiskerRight M) N) (-transformComponent (hξ.whiskerLeft K) N)
    (transformComponent (hσ.whiskerRight M) N)
    (inductionTripleFlattening_prefix_rectangular J V K W M hσ' N)
    (grid_negative_square _ _ _ (inductionTripleFlattening_suffix_rectangular K W M W M hξ N))
    (inductionTripleFlattening_prefix_rectangular K W J V M hσ N)
  have hrow : gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N ≫ e.hom =
      e.hom ≫ gridDirectMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N :=
    grid_difference_square _ _ _ _ _ hR hL
  exact (inductionEndConjugation_of_square e _ _ hrow).symm

variable {α : ∀ s, End (J.obj s)} {β : ∀ s, End (V.obj s)} {γ : ∀ s, End (M.obj s)}
  (hα : IsSupernatural k (D.parity i) α) (hβ : IsSupernatural k (D.parity j) β)
  (hγ : IsSupernatural k (D.parity i) γ)

/-- The whole grid correction, with the literal source equation exposed at this generic intermediate. -/
theorem gridMixedBraid_polynomial (hij : i ≠ j)
    (hsource : ∀ s,
      (show End ((F₀).obj s) from M.map (σ s) ≫ ξ (K.obj s) ≫ M.map (σ' s)) -
      (show End ((F₀).obj s) from ρ (J.obj s) ≫ L.map (τ s) ≫ ρ' (J.obj s)) =
        tripleDotCorrectionPolynomial D (parameterTwist D Sc) (R := End ((F₀).obj s)) i j
          (γ ((J ⋙ V).obj s)) (M.map (β (J.obj s))) (M.map (V.map (α s))))
    (N : Superfunctor k C (SVec k)) :
    gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N =
      tripleDotCorrectionPolynomial D Sc (R := End (induced M (induced V (induced J N)))) i j
        ((induction M).map ((induction V).map (dotEnd J hα N)))
        ((induction M).map (dotEnd V hβ ((induction J).obj N)))
        (dotEnd M hγ ((induction V).obj ((induction J).obj N))) := by
  have hd := transformComponent_corrected_braid F₀ F₁ F₂ D Sc i j
    ((hα.whiskerRight V).whiskerRight M) ((hβ.whiskerLeft J).whiskerRight M)
    (hγ.whiskerLeft (J ⋙ V))
    (hσ.whiskerRight M) (hξ.whiskerLeft K) (hσ'.whiskerRight M)
    (hρ.whiskerLeft J) (hτ.whiskerRight L) (hρ'.whiskerLeft J) hsource hij N
  have hp := transformComponent_triplePolynomial F₀ D Sc i j
    ((hα.whiskerRight V).whiskerRight M) ((hβ.whiskerLeft J).whiskerRight M)
    (hγ.whiskerLeft (J ⋙ V)) hij N
  have ht := inductionTripleFlattening_polynomial D Sc i j J V M hα hβ hγ hij N
  rw [gridMixedBraid_conjugate]
  change inductionEndConjugation (k := k) (inductionTripleFlattening J V M N) _ = _
  rw [show gridDirectMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N = _ from hd, hp]
  exact ht.symm

end OddMath.QuiverHecke.ELVOld.BalancedInduction
