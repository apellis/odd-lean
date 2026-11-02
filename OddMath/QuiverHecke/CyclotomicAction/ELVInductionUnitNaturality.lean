import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction

/-! # Even induction maps are determined on unit generators
The scalar and weighted append tensor comparisons in SwappedVacuumCoordinates §6
reduce to their unit formulas through this coend naturality identity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {D : Type u} [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]

private theorem even_total_naturality_apply
    {F H : Superfunctor k D (SVec k)} (f : F ⟶ H)
    (hf : f ∈ parity (R := k) F H 0) {v w : D} (g : v ⟶ w) (b : F.obj v) :
    f.total w (F.map g b) = H.map g (f.total v b) := by
  have hz (t : D) : f.total t = f.app 0 t := by
    change f.app 0 t + f.app 1 t = f.app 0 t
    rw [Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  rw [hz v, hz w]
  have h := ((Superfunctor.toSuperNatTrans f).isSupernatural 0).naturality_zero g
  simpa only [SVec.comp_apply] using
    congrArg (fun a : F.obj v ⟶ H.obj w => a b) h

variable {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (M : Superfunctor k C (SVec k))

/-- Evaluating an even module map on any old tensor needs only its value on
the unit. No unit-compatibility or homogeneity premise on the tensor arrow is assumed. -/
theorem moduleMorphism_total_tensor_even
    {H : Superfunctor k D (SVec k)} (f : induced J M ⟶ H)
    (hf : f ∈ parity (R := k) _ _ 0)
    (v : C) (w : D) (g : J.obj v ⟶ w) (b : M.obj v) :
    f.total w (tensor J M.toFunctor v g b) =
      H.map g (f.total (J.obj v) (unit J M.toFunctor v b)) :=
  (congrArg (f.total w) (postcompose_unit J M.toFunctor g b)).symm.trans
    (even_total_naturality_apply f hf g (unit J M.toFunctor v b))

end OddMath.QuiverHecke.ELVOld.BalancedInduction
