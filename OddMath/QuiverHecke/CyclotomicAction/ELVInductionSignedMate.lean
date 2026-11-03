import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularMate
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMateComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedMateLinear

/-! # The signed grid mate as a rectangular mate

Brundan–Ellis (1.13)–(1.14): the diagonal ordinary cup-crossing-cap is
the rectangular mate of the negative crossing. This identifies the
prescribed diagonal fields with the full-inclusion comparison theorem.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem coend_ext
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    {f g : Obj J M w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      f (tensor J M s a b) = g (tensor J M s a b)) : f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

omit [Preadditive A] [Linear k A] [Supercategory k A]
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K] in
private theorem negativeFamily (hx : IsSupernatural k p α) : IsSupernatural k p (fun s => -α s) where
  mem s := neg_mem (hx.mem s)
  naturality hf := by
    rw [Preadditive.comp_neg, hx.naturality hf, Preadditive.neg_comp, smul_neg]

/-- The prescribed whole grid mate is the rectangular mate of the negative crossing. -/
theorem rectangularMate_negative_eq_grid (N : Superfunctor k A (SVec k)) (t : A) :
    orderedRectangularMateLinear J J K K (negativeFamily J K hα) N t =
      orderedGridMateLinear J K hα N t := by
  apply coend_ext _ _
  intro s g b
  rw [orderedRectangularMateLinear_tensor, orderedGridMateLinear_tensor, Preadditive.neg_comp]

/-- Changing the degree by its equality changes no prescribed grid mate map. -/
theorem gridMateLinear_degree_eq {r : ZMod 2} (hp : p = r)
    (hr : IsSupernatural k r α) (N : Superfunctor k A (SVec k)) (t : A) :
    orderedGridMateLinear J K hα N t = orderedGridMateLinear J K hr N t := by
  cases hp
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  {p : ZMod 2} {α : ∀ s, (A ⋙ A).obj s ⟶ (A ⋙ A).obj s}
  (hα : IsSupernatural k p α)

omit [A.Additive] [A.Linear k] [IsSuperfunctor k A] in
private theorem negativeFamily (hx : IsSupernatural k p α) : IsSupernatural k p (fun s => -α s) where
  mem s := neg_mem (hx.mem s)
  naturality hf := by
    rw [Preadditive.comp_neg, hx.naturality hf, Preadditive.neg_comp, smul_neg]

/-- The negative-crossing ordinary mixed mate is the prescribed global diagonal mate. -/
theorem mixedMate_negative_eq_ordered (N : Superfunctor k C (SVec k)) (t : C) :
    orderedMixedMateCoend A A (negativeFamily A hα) N t =
      orderedMateLinear A hα N t := by
  apply coend_ext _ _
  intro s g b
  have hL := orderedMixedMateCoend_tensor A A (negativeFamily A hα) N s t g b
  have hs : tensor A (A ⋙ N.toFunctor) s g b =
      tensor A ((restriction A).obj N).toFunctor s g b := rfl
  have hR := congrArg (orderedMateLinear A hα N t) hs
  have hR₂ := orderedMateLinear_tensor A hα N s t g b
  have hn : tensor A N.toFunctor (A.obj s) ((-α s) ≫ twist k p (A.map g)) b =
      -tensor A N.toFunctor (A.obj s) (α s ≫ twist k p (A.map g)) b := by
    rw [Preadditive.neg_comp]
    change inclusion A N.toFunctor (A.obj t) (A.obj s)
      ((-(α s ≫ twist k p (A.map g))) ⊗ₜ[k] b) = _
    rw [TensorProduct.neg_tmul, map_neg]
    rfl
  exact hL.trans (hn.trans (hR.trans hR₂).symm)

end OddMath.QuiverHecke.ELVOld
