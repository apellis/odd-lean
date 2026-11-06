import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence
import OddMath.QuiverHecke.CyclotomicAction.ELVOldModuleAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCrossTensor

/-! Selected recursive word comparisons and the actual signed equal-colour
crossing, via existing whole-comparison coherence and outer recasting. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordPair
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (i : I)

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

section Recursive
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) (K : B ⥤ B) (P Q : C ⥤ B)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P.Additive] [P.Linear k] [IsSuperfunctor k P]
  [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (eP : J ⋙ K = P) (eQ : P ⋙ K = Q) (R : Superfunctor k C (SVec k))
end Recursive

section Outer
private theorem total_of_mem {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : C) : f.total z = f.app p z := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]
private theorem homogeneous_total_ext {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f g : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ p)
    (h : ∀ z, f.total z = g.total z) : f = g := by
  apply SuperNatTrans.ext
  funext q z
  by_cases hq : q = p
  · subst q
    rw [← total_of_mem hf, ← total_of_mem hg]
    exact h z
  · rw [Superfunctor.app_eq_zero_of_mem hf hq, Superfunctor.app_eq_zero_of_mem hg hq]

end Outer

section Signed
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) (K : B ⥤ B) (P Q : C ⥤ B)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P.Additive] [P.Linear k] [IsSuperfunctor k P]
  [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (eP : J ⋙ K = P) (eQ : P ⋙ K = Q) (R : Superfunctor k C (SVec k))
  (e : J ⋙ (K ⋙ K) = Q) {p : ZMod 2}
  {β : ∀ w, (K ⋙ K).obj w ⟶ (K ⋙ K).obj w} (hβ : IsSupernatural k p β)
  {α : ∀ v, Q.obj v ⟶ Q.obj v} (hα : IsSupernatural k p α)

end Signed

end OddMath.QuiverHecke.ELVOld.PowerWordPair
