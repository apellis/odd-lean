import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMate

/-! # Literal coend values of the chosen changing-content crossing mate

The scalar and fixed-content comparisons of the prescribed first matrix
entry in DeformedMatrixComparison (2), (4) need the same given mate on raw
coends. These formulas expose its carriers before substituting concrete
append functors and put the extra minus into the coefficient arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- The literal coend map of the chosen unit, signed crossing and counit. -/
def orderedGridMateLinear
    {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hα : IsSupernatural k p α) (N : Superfunctor k A (SVec k)) (t : A) :
    Obj J ((restriction J).obj N).toFunctor t →ₗ[k] Obj K N.toFunctor (K.obj t) :=
  (orderedGridMateComponent J K hα N).total t

/-- The extra minus belongs to the complete crossed coefficient; neither
coefficient arrow nor module vector needs to be homogeneous. -/
theorem orderedGridMateLinear_tensor
    {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hα : IsSupernatural k p α) (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    orderedGridMateLinear J K hα N t
      (tensor J ((restriction J).obj N).toFunctor s g b) =
      tensor K N.toFunctor (J.obj s) (-(α s ≫ twist k p (K.map g))) b := by
  have h := orderedGridMateComponent_total_tensor J K hα N s t g b
  have hn : tensor K N.toFunctor (J.obj s) (-(α s ≫ twist k p (K.map g))) b =
      -tensor K N.toFunctor (J.obj s) (α s ≫ twist k p (K.map g)) b := by
    change inclusion K N.toFunctor (K.obj t) (J.obj s)
        ((-(α s ≫ twist k p (K.map g))) ⊗ₜ[k] b) =
      -inclusion K N.toFunctor (K.obj t) (J.obj s)
        ((α s ≫ twist k p (K.map g)) ⊗ₜ[k] b)
    rw [TensorProduct.neg_tmul, map_neg]
  set_option backward.dsimp.instances true in
    dsimp only [orderedGridMateLinear, induction] at h ⊢
  exact h.trans hn.symm

end OddMath.QuiverHecke.ELVOld.BalancedInduction
