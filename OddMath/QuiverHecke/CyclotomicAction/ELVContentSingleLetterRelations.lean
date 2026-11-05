/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCompositeComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentOperatorQuadratic

/-! # Single-letter content induction relations

Advances `DeformedActionAssembly.md` §5 by transporting the checked normalized
source crossing and positioned dots through the canonical even comparison.
`contentEPair_quadratic` is the original-Sc ordered polynomial relation on
successive single-letter induction, for every module. The second target content
is explicitly recast, not silently identified. `contentEPairCrossTransform`
is supernatural against odd module maps and `contentEPairCross_total` identifies
its evaluated map. No triple coherence, mixed braid, weight assembly or
nondegeneracy is asserted in this module.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Evaluation of a module isomorphism on the entire superspace. -/
def moduleIsoLinearEquiv {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M L : Superfunctor k C (SVec k)} (e : M ≅ L) (w : C) : M.obj w ≃ₗ[k] L.obj w where
  toLinearMap := e.hom.total w
  invFun := e.inv.total w
  left_inv x := by
    have h := congrArg (fun f : M ⟶ M => f.total w) e.hom_inv_id
    rw [Superfunctor.comp_total] at h
    simp only [SuperNatTrans.total, Superfunctor.id_app_zero,
      Superfunctor.id_app_one, add_zero] at h
    exact congrArg (fun f : M.obj w →ₗ[k] M.obj w => f x) h
  right_inv x := by
    have h := congrArg (fun f : L ⟶ L => f.total w) e.inv_hom_id
    rw [Superfunctor.comp_total] at h
    simp only [SuperNatTrans.total, Superfunctor.id_app_zero,
      Superfunctor.id_app_one, add_zero] at h
    exact congrArg (fun f : L.obj w →ₗ[k] L.obj w => f x) h

/-- The second single-letter induction has its target content explicitly transported. -/
abbrev contentEPairTo (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) :=
  contentE D Sc cutoff N β i ⋙
    contentInductionTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ
      (by rw [add_assoc]; exact h)

def contentEPairToComparison (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) :
    contentEPairTo D Sc cutoff N β i j γ h ≅ contentInductionTo D Sc cutoff N β [i,j] γ h :=
  contentInductionComp D Sc cutoff N β [i] [j] γ _ h

/-- Transport of a homogeneous transformation through even natural comparisons. -/
theorem evenComparison_supernatural
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G F' G' : C ⥤ B}
    [F.Additive] [F.Linear k] [G.Additive] [G.Linear k]
    [F'.Additive] [F'.Linear k] [G'.Additive] [G'.Linear k]
    (e : F' ≅ F) (f : G' ≅ G)
    (he : ∀ M, EvenComparisonAt (k := k) e M)
    (hf : ∀ M, EvenComparisonAt (k := k) f M)
    {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M} (hx : IsSupernatural k p x) :
    IsSupernatural k p (fun M => (e.hom.app M ≫ x M) ≫ f.inv.app M) := by
  simpa only [zero_add, add_zero] using
    ((isSupernatural_of_natTrans e.hom (fun M => (he M).1)).comp hx).comp
      (isSupernatural_of_natTrans f.inv (fun M => (hf M).2))

private theorem homogeneous_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (M : C) : hx.toSuperNatTrans.total M = x M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

end OddMath.QuiverHecke.ELVOld

