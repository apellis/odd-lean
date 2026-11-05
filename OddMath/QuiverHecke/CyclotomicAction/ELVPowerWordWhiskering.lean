import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordPairCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleMate
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Selected word comparison and induction of signed old-Hom maps

SwappedVacuumCoordinates §§4–5 require compatibility with arbitrary right
contexts, beyond the last dot and crossing. The selected append comparison
is used to identify the independently induced old-Hom module map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWhiskering
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (s t : List I) (i : I)

private def comparisonIso {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (P : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (e : J ⋙ K = P)
    (R : Superfunctor k C (SVec k)) :
    (BalancedInduction.induction K).obj (BalancedInduction.induced J R) ≅
      (BalancedInduction.induction P).obj R := (inductionCompOfEq J K P e).app R

private theorem total_of_mem {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : C) : f.total z = f.app p z := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]
section Inner
variable {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J₀ J₁ : C ⥤ B) (K : B ⥤ E) (P₀ P₁ : C ⥤ E)
  [J₀.Additive] [J₀.Linear k] [IsSuperfunctor k J₀]
  [J₁.Additive] [J₁.Linear k] [IsSuperfunctor k J₁]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P₀.Additive] [P₀.Linear k] [IsSuperfunctor k P₀]
  [P₁.Additive] [P₁.Linear k] [IsSuperfunctor k P₁]
  (e₀ : J₀ ⋙ K = P₀) (e₁ : J₁ ⋙ K = P₁)
  {p : ZMod 2} {α : ∀ v, J₀.obj v ⟶ J₁.obj v} (hα : IsSupernatural k p α)
  {β : ∀ v, P₀.obj v ⟶ P₁.obj v} (hβ : IsSupernatural k p β)
  (R : Superfunctor k C (SVec k))
end Inner

section Chosen
variable {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J₀ J₁ : C ⥤ B) (K : B ⥤ E) (P₀ P₁ : C ⥤ E)
  [J₀.Additive] [J₀.Linear k] [IsSuperfunctor k J₀]
  [J₁.Additive] [J₁.Linear k] [IsSuperfunctor k J₁]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P₀.Additive] [P₀.Linear k] [IsSuperfunctor k P₀]
  [P₁.Additive] [P₁.Linear k] [IsSuperfunctor k P₁]
  (e₀ : J₀ ⋙ K = P₀) (e₁ : J₁ ⋙ K = P₁)
  {p : ZMod 2} {α : ∀ v, J₀.obj v ⟶ J₁.obj v} (hα : IsSupernatural k p α)
  {β : ∀ v, P₀.obj v ⟶ P₁.obj v} (hβ : IsSupernatural k p β)
  (R : Superfunctor k C (SVec k))
end Chosen

end OddMath.QuiverHecke.ELVOld.PowerWordWhiskering
