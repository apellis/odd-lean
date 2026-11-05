/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization

/-! # The suffix pair crossing as a natural family

This supplies the other independently induced crossing family required by the
three-factor braid fields of Brundan–Ellis Definition 1.5.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Total components detect a supernatural transformation, without a
homogeneity assumption. Used twice for module-valued natural families. -/
theorem BalancedInduction.supernatural_ext_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {f g : SuperNatTrans k F G}
    (h : ∀ M, f.total M = g.total M) : f = g := by
  apply SuperNatTrans.ext
  funext p M
  have hp (t : SuperNatTrans k F G) : proj k p (t.total M) = t.app p M := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact proj_eq_of_add rfl (t.app_mem 0 M) (t.app_mem 1 M)
    · exact proj_eq_of_add (add_comm _ _) (t.app_mem 1 M)
        (by simpa using t.app_mem 0 M)
  rw [← hp f, ← hp g, h M]

section Suffix
variable (β : Multiset I) (i j l : I) (γ : Multiset I)
  (h : β + ([i,j,l] : Multiset I) = γ)
  (ht : β + ([i,l,j] : Multiset I) = γ)

private theorem family_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (M : C) :
    hx.toSuperNatTrans.total M = x M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

end Suffix
end OddMath.QuiverHecke.ELVOld
