/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMate

/-! # Homogeneity of the changing-category crossing mate

DeformedMatrixComparison (2), (4) uses the prescribed ordered mate in
parity-shifted matrix coordinates. Its degree follows from the given
crossing, even induction comparisons and even ordinary adjunction maps.
No invertibility of the mate is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem even_comp_homogeneous_comp_even
    {k : Type u} [CommRing k] {E : Type*} [Category E]
    [Preadditive E] [Linear k E] [Supercategory k E]
    {a b c d : E} {p : ZMod 2} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    (hf : f ∈ parity (R := k) _ _ 0) (hg : g ∈ parity (R := k) _ _ p)
    (hh : h ∈ parity (R := k) _ _ 0) :
    f ≫ g ≫ h ∈ parity (R := k) _ _ p := by
  simpa only [zero_add, add_zero] using comp_mem hf (comp_mem hg hh)

variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

/-- Both flattening comparisons are even, so the prescribed double
crossing retains the given crossing degree. -/
theorem gridDoubleCrossComponent_mem (M : Superfunctor k C (SVec k)) :
    gridDoubleCrossComponent J K hα M ∈ parity (R := k) _ _ p := by
  unfold gridDoubleCrossComponent
  exact even_comp_homogeneous_comp_even (inductionComp_hom_mem J K M)
    (transformComponent_mem hα M) (inductionComp_inv_mem J K M)

/-- The ordinary unit, signed crossing and induced counit have degrees
zero, p and zero respectively. -/
theorem orderedGridMateComponent_mem (N : Superfunctor k A (SVec k)) :
    orderedGridMateComponent J K hα N ∈ parity (R := k) _ _ p := by
  unfold orderedGridMateComponent
  exact even_comp_homogeneous_comp_even
    (adjunctionUnit_mem K (induced J ((restriction J).obj N)))
    (map_mem (restriction K)
      (Submodule.neg_mem _ (gridDoubleCrossComponent_mem J K hα ((restriction J).obj N))))
    (map_mem (restriction K) (map_mem (induction K) (adjunctionCounit_mem J N)))

end OddMath.QuiverHecke.ELVOld.BalancedInduction
