import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction
import OddMath.SKM.RouquierNormalizedHomAdjunction

/-! # Canonical parity coordinates under module restriction comparison

The shifted unit/cap entries of DeformedMatrixComparison (5), (6) use the
existing parity shifts with their full module actions. Restricting the
ordinary shifted module and then comparing its value must agree with the
chosen old shifted target. The bridge below uses the canonical
`homParityShiftCommute`; its two odd coordinate maps cancel their degrees.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u v w
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (Q : C ⥤ D) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
local instance sourceModulePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
local instance targetModulePi : PiSupercategory k (Superfunctor k D (SVec k)) :=
  supermodulePiSupercategory
local notation "S₀" => SKM.homParityShift (k := k) (C := Superfunctor k C (SVec k))
local notation "S₁" => SKM.homParityShift (k := k) (C := Superfunctor k D (SVec k))
local notation "P₀" => SKM.homParityShiftDatum (k := k) (C := Superfunctor k C (SVec k))
local notation "P₁" => SKM.homParityShiftDatum (k := k) (C := Superfunctor k D (SVec k))

section Components
variable (M : Superfunctor k D (SVec k)) (N : Superfunctor k C (SVec k))
  (e : (restriction Q).obj M ≅ N)

end Components

section Families
variable {X : Type v} [Category.{w} X]
  (F : X ⥤ Superfunctor k D (SVec k)) (G : X ⥤ Superfunctor k C (SVec k))
  (e : F ⋙ restriction Q ≅ G)

end Families
end OddMath.QuiverHecke.ELVOld.BalancedInduction
