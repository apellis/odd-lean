/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCompositeComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularMate

/-! # Induction crossing comparison under append equalities

The comparison needed to transport Brundan–Ellis (1.12) to weight
products identifies the word-induction crossing with the rectangular
crossing. Append equalities are retained as whole functor equalities
before specializing to successor content certificates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Category.{u} A] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (F G : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  [G.Additive] [G.Linear k] [IsSuperfunctor k G]
  (hF : J ⋙ L = F) (hG : K ⋙ U = G)
  {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ U).obj s}
  {β : ∀ s, F.obj s ⟶ G.obj s}
  (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β)

private theorem inductionCompOfEq_refl (P : C ⥤ A) (Q : A ⥤ E)
    [P.Additive] [P.Linear k] [IsSuperfunctor k P]
    [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q] :
    inductionCompOfEq (k := k) P Q (P ⋙ Q) rfl = BalancedInduction.inductionComp P Q := by
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl]

/-- Flattening to a word, applying its crossing, and expanding is the
rectangular crossing when its coefficient is the transported word crossing. -/
theorem inductionCompOfEq_cross
    (hcoeff : ∀ s, α s = eqToHom (congrArg (fun H : C ⥤ E => H.obj s) hF) ≫
      β s ≫ eqToHom (congrArg (fun H : C ⥤ E => H.obj s) hG).symm)
    (P : Superfunctor k C (SVec k)) :
    ((inductionCompOfEq K U G hG).hom.app P ≫
      BalancedInduction.transformComponent hβ P) ≫
        (inductionCompOfEq J L F hF).inv.app P =
      BalancedInduction.rectangularCrossComponent J K L U hα P := by
  subst F
  subst G
  have hαβ : α = β := by
    funext s
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hcoeff s
  subst β
  rw [inductionCompOfEq_refl, inductionCompOfEq_refl]
  exact Category.assoc _ _ _

/-- A homogeneous induction transformation has its given component in its own degree. -/
theorem inductionTransform_app_self (P : Superfunctor k C (SVec k)) :
    (BalancedInduction.transform hβ).app p P = BalancedInduction.transformComponent hβ P := by
  simp only [BalancedInduction.transform, IsSupernatural.toSuperNatTrans, ↓reduceIte]

end OddMath.QuiverHecke.ELVOld
