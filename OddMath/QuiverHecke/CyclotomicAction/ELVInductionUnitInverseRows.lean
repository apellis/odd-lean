import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitColumnModules

/-! # Inverse rows of the finite dotted-unit module matrix

Brundan–Ellis (1.13) at the empty boundary. Project the specified even
module inverse and remove the original source shift. The resulting rows
have the prescribed finite Kronecker window and reconstruct the target.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k)) (m : ℕ)
local instance unitInverseRowsPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
private def sourceUnshift (q : ZMod 2) (N : Superfunctor k C (SVec k)) (n : ℕ) (r : Fin n) :
    (unitColumnModuleFamily q N n r) ≅ N :=
  (SKM.homParityShiftDatum (k := k) (r.val • q)).iso N

private theorem sourceUnshift_mem (q : ZMod 2) (N : Superfunctor k C (SVec k)) (n : ℕ) (r : Fin n) :
    (sourceUnshift q N n r).hom ∈ parity (R := k) _ _ (r.val • q) :=
  (SKM.homParityShiftDatum (k := k) (r.val • q)).hom_mem N

local notation "rIso" => sourceUnshift p M m
local notation "rParity" => (fun r : Fin m => Fin.val r • p)
local notation "rMem" => sourceUnshift_mem p M m
local notation "column" => (fun r : Fin m => unitDotColumn J hα M (Fin.val r))
local notation "columnMem" => (fun r : Fin m => unitDotColumn_mem J hα M (Fin.val r))

private theorem unitModuleMap_restored : unitColumnModuleMap J hα M m =
    OddMath.FiniteSupermodule.restoredColumns rIso rParity rMem column columnMem := rfl

variable (e : OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ≅
    (restriction J).obj ((induction J).obj M))
  (he : e.hom = unitColumnModuleMap J hα M m)

/-- The inverse row in the original unshifted value coordinates. -/
def unitColumnModuleInverseRow (r : Fin m) :
    (restriction J).obj ((induction J).obj M) ⟶ M :=
  OddMath.FiniteSupermodule.inverseCoordinateRow rIso e r

include he in
/-- The finite ordinary unit columns and extracted inverse rows are dual. -/
theorem unitDotColumn_inverseRow (a r : Fin m) :
    unitDotColumn J hα M a.val ≫ unitColumnModuleInverseRow J M m e r =
      if a = r then 𝟙 M else 0 := by
  classical
  by_cases har : a = r
  · subst a
    rw [ite_eq_left rfl]
    exact OddMath.FiniteSupermodule.forward_inverseCoordinateRow rIso rParity rMem column columnMem e
      (he.trans (unitModuleMap_restored J hα M m)) r
  · rw [ite_eq_right har]
    exact OddMath.FiniteSupermodule.forward_inverseCoordinateRow_ne rIso rParity rMem column columnMem e
      (he.trans (unitModuleMap_restored J hα M m)) a r har

include he in
/-- The extracted rows and prescribed ordinary columns give the finite
boundary decomposition, including m=0. -/
theorem sum_unitColumnModuleInverseRow_unitDotColumn :
    (∑ r : Fin m, unitColumnModuleInverseRow J M m e r ≫ unitDotColumn J hα M r.val) =
      𝟙 ((restriction J).obj ((induction J).obj M)) :=
  OddMath.FiniteSupermodule.sum_inverseCoordinateRow_forward rIso rParity rMem column columnMem e
    (he.trans (unitModuleMap_restored J hα M m))

end OddMath.QuiverHecke.ELVOld.BalancedInduction
