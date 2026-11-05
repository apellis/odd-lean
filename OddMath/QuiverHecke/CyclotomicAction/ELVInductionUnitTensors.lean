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
