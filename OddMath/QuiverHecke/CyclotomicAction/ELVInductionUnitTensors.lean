import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp

/-! # Unit tensors under composition of balanced induction
These formulas supply the unit-generator computation for the scalar and
weighted append comparisons in SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (M : Superfunctor k C (SVec k))

/-- The canonical flattening sends the nested unit to the composite unit. -/
theorem inductionComp_hom_total_unit (v : C) (b : M.obj v) :
    ((inductionComp J K).hom.app M).total (K.obj (J.obj v))
      (unit K (induced J M).toFunctor (J.obj v) (unit J M.toFunctor v b)) =
      unit (J ⋙ K) M.toFunctor v b := by
  change ((inductionComp J K).hom.app M).total (K.obj (J.obj v))
    (tensor K (induced J M).toFunctor (J.obj v) (𝟙 _)
      (tensor J M.toFunctor v (𝟙 _) b)) = _
  rw [inductionComp_hom_total_tensor, K.map_id, Category.id_comp]
  rfl

/-- The canonical unflattening sends the composite unit to the nested unit. -/
theorem inductionComp_inv_total_unit (v : C) (b : M.obj v) :
    ((inductionComp J K).inv.app M).total ((J ⋙ K).obj v)
      (unit (J ⋙ K) M.toFunctor v b) =
      unit K (induced J M).toFunctor (J.obj v) (unit J M.toFunctor v b) :=
  inductionComp_inv_total_tensor J K M v ((J ⋙ K).obj v) (𝟙 _) b

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]

/-- An even input-module map acts on the literal tensor without a parity twist. -/
theorem moduleMap_total_tensor_even
    {M L : Superfunctor k C (SVec k)} (f : M ⟶ L)
    (hf : f ∈ parity (R := k) _ _ 0) (w : D) (v : C)
    (g : J.obj v ⟶ w) (b : M.obj v) :
    (moduleMap J f).total w (tensor J M.toFunctor v g b) =
      tensor J L.toFunctor v g (f.app 0 v b) := by
  rw [moduleMap_total_tensor, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide),
    LinearMap.zero_apply, tensor_zero_right, add_zero]

end OddMath.QuiverHecke.ELVOld.BalancedInduction
