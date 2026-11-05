import OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixSquares
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeShiftedUnitComparison
import OddMath.Algebra.FiniteSuperspace

/-! # Finite matrices of the prescribed shifted unit columns

The missing-colour case of Brundan--Ellis (1.13) has only the finite unit
columns. Canonical parity coordinates turn the unshifted unit-column chart
square into its actual finite column square, before specializing categories
or induced module carriers.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
section Families
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
local instance unitColumnFamilyPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- The finite canonical shifted value family, with no principal E/F slot. -/
def unitColumnSourceSpace (p : ZMod 2) (M : Superfunctor k C (SVec k))
    (m : ℕ) (w : C) : SVec k :=
  OddMath.FiniteSuperspace.product fun r : Fin m =>
    ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w
end Families

section Columns
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k))
local instance unitColumnComponentPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- The literal finite assembly of the given canonically shifted unit columns. -/
def unitColumnMatrix (m : ℕ) (w : C) :
    unitColumnSourceSpace p M m w ⟶ ((restriction J).obj ((induction J).obj M)).obj w :=
  OddMath.FiniteSuperspace.assembleColumns
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w)
    (((restriction J).obj ((induction J).obj M)).obj w)
    (fun r => (shiftedUnitDotColumn J hα M r.val).total w)

private theorem unitColumn_total (n : ℕ) (w : C) :
    SVec.toLinearMap ((shiftedUnitDotColumn J hα M n).total w) =
      unitDotLinear J hα M n w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (n • p)).iso M).hom.total w) :=
  shiftedUnitDotColumn_total J hα M n w

end Columns

section Coordinates
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v)
local instance unitColumnCoordinateSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
local instance unitColumnCoordinateTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) :=
  supermodulePiSupercategory

/-- The whole finite family chart uses the given plain value equivalence
inside each pair of canonical source/target parity coordinates. -/
def unitColumnFamilyEquiv (p : ZMod 2) (m : ℕ) :
    unitColumnSourceSpace p M m w ≃ₗ[k] unitColumnSourceSpace p N m v :=
  LinearEquiv.piCongrRight fun r : Fin m =>
    shiftedModuleValueLinearEquiv M N w v e (r.val • p)

end Coordinates

private theorem unitColumns_square
    {k : Type u} [CommRing k] {ι : Type} [Fintype ι]
    (V W : ι → SVec k) (X Y : SVec k) (e : ∀ a, V a ≃ₗ[k] W a)
    (c : X →ₗ[k] Y) (f : ∀ a, V a ⟶ X) (g : ∀ a, W a ⟶ Y)
    (h : ∀ a, c ∘ₗ SVec.toLinearMap (f a) = SVec.toLinearMap (g a) ∘ₗ (e a).toLinearMap) :
    c ∘ₗ SVec.toLinearMap (OddMath.FiniteSuperspace.assembleColumns V X f) =
      SVec.toLinearMap (OddMath.FiniteSuperspace.assembleColumns W Y g) ∘ₗ
        (LinearEquiv.piCongrRight e).toLinearMap := by
  apply LinearMap.ext
  intro x
  change c (∑ a, f a (x a)) = ∑ a, g a (e a (x a))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact LinearMap.congr_fun (h a) (x a)

section Comparison
variable {k C A D B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (T : D ⥤ B) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v)
  (c : Obj J M.toFunctor (J.obj w) →ₗ[k] Obj T N.toFunctor (T.obj v))
local instance unitColumnSquareSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
local instance unitColumnSquareTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) :=
  supermodulePiSupercategory

/-- Canonical parity coordinates and finite sums transport the actual unit
matrix whenever its unshifted dotted columns commute with the given charts. -/
theorem unitColumnMatrix_square
    (h : ∀ n, c ∘ₗ unitDotLinear J hα M n w = unitDotLinear T hβ N n v ∘ₗ e.toLinearMap)
    (m : ℕ) :
    c ∘ₗ SVec.toLinearMap (unitColumnMatrix J hα M m w) =
      SVec.toLinearMap (unitColumnMatrix T hβ N m v) ∘ₗ
        (unitColumnFamilyEquiv M N w v e p m).toLinearMap := by
  apply unitColumns_square
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w)
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj N).obj v)
    (((restriction J).obj ((induction J).obj M)).obj w)
    (((restriction T).obj ((induction T).obj N)).obj v)
    (fun r => shiftedModuleValueLinearEquiv M N w v e (r.val • p))
    c (fun r => (shiftedUnitDotColumn J hα M r.val).total w)
    (fun r => (shiftedUnitDotColumn T hβ N r.val).total v)
  intro r
  exact linearColumn_parity_square _ _ _ _ _ _ _ _ _ (h r.val)
    (shiftedModuleValueLinearEquiv_source_square M N w v e (r.val • p))
    (unitColumn_total J hα M r.val w) (unitColumn_total T hβ N r.val v)
end Comparison
end OddMath.QuiverHecke.ELVOld.BalancedInduction
