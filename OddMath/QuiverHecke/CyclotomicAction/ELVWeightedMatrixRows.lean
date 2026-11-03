import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVOperatorPowerComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVMatrixEntryTotals

/-! # Dotted rows under the weighted matrix charts

DeformedMatrixComparison (2), (4) uses the ordinary unit/dot columns and
dot/counit rows. The same prescribed module maps are evaluated on literal
coends before the selected weighted source and target charts are applied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

/-- The actual ordinary unit followed by the restricted dot power. -/
def unitDotColumn (M : Superfunctor k C (SVec k)) (n : ℕ) :
    M ⟶ (restriction J).obj ((induction J).obj M) :=
  (adjunction J).unit.app M ≫ (restriction J).map ((transformComponent hα M) ^ n)

/-- The actual dot power followed by the ordinary counit. -/
def capDotRow (N : Superfunctor k A (SVec k)) (n : ℕ) :
    (induction J).obj ((restriction J).obj N) ⟶ N :=
  ((transformComponent hα ((restriction J).obj N)) ^ n) ≫ (adjunction J).counit.app N

theorem transform_power_mem (M : Superfunctor k C (SVec k)) (n : ℕ) :
    (transformComponent hα M) ^ n ∈ parity (R := k) _ _ (n • p) := by
  induction n with
  | zero =>
    simp only [pow_zero, End.one_def, zero_nsmul]
    exact id_mem _
  | succ n ih =>
    rw [pow_succ, End.mul_def]
    simpa only [succ_nsmul, add_comm] using comp_mem (transformComponent_mem hα M) ih

theorem unitDotColumn_mem (M : Superfunctor k C (SVec k)) (n : ℕ) :
    unitDotColumn J hα M n ∈ parity (R := k) _ _ (n • p) := by
  have h := comp_mem (adjunctionUnit_mem J M)
    (IsSuperfunctor.map_mem (F := restriction J) (transform_power_mem J hα M n))
  simpa only [unitDotColumn, zero_add] using h

theorem capDotRow_mem (N : Superfunctor k A (SVec k)) (n : ℕ) :
    capDotRow J hα N n ∈ parity (R := k) _ _ (n • p) := by
  simpa only [capDotRow, add_zero] using comp_mem
    (transform_power_mem J hα ((restriction J).obj N) n) (adjunctionCounit_mem J N)

private theorem total_power {F : Superfunctor k A (SVec k)} (f : End F) (w : A) (n : ℕ) :
    SVec.toLinearMap ((f ^ n).total w) = (SVec.toLinearMap (f.total w)) ^ n := by
  induction n with
  | zero =>
    change SVec.toLinearMap (SuperNatTrans.id F.toFunctor |>.total w) = LinearMap.id
    rw [SuperNatTrans.id_total, SVec.toLinearMap_id]
  | succ n ih =>
    rw [pow_succ, End.mul_def, Superfunctor.comp_total, SVec.toLinearMap_comp, ih, pow_succ]
    rfl

private theorem transform_total (M : Superfunctor k C (SVec k)) (w : A) :
    SVec.toLinearMap ((transformComponent hα M).total w) = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app, ite_true, ite_false,
      zero_ne_one, one_ne_zero, zero_add, add_zero, SVec.toLinearMap]

private theorem transform_power_total (M : Superfunctor k C (SVec k)) (w : A) (n : ℕ) :
    SVec.toLinearMap (((transformComponent hα M) ^ n).total w) = (transformLinear hα M w) ^ n := by
  have h := total_power (transformComponent hα M) w n
  rw [transform_total] at h
  exact h

private theorem restriction_total {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) :
    ((restriction J).map f).total w = f.total (J.obj w) := rfl

private theorem unit_total (M : Superfunctor k C (SVec k)) (w : C) :
    SVec.toLinearMap (((adjunction J).unit.app M).total w) = unit J M.toFunctor w := by
  change SVec.toLinearMap (((adjunctionUnit J).app M).total w) = _
  simp only [adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ite_true, one_ne_zero, ite_false, add_zero, SVec.toLinearMap]
  rfl

private theorem counit_total (N : Superfunctor k A (SVec k)) (w : A) :
    SVec.toLinearMap (((adjunction J).counit.app N).total w) = restrictionCounitLinear J N w := by
  change SVec.toLinearMap (((adjunctionCounit J).app N).total w) = _
  simp only [adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ite_true, one_ne_zero, ite_false, add_zero, SVec.toLinearMap]
  rfl

/-- Literal unit/dot component of the given ordinary module column. -/
def unitDotLinear (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    M.obj w →ₗ[k] Obj J M.toFunctor (J.obj w) :=
  ((transformLinear hα M (J.obj w)) ^ n) ∘ₗ unit J M.toFunctor w

/-- Literal dot/counit component of the given ordinary module row. -/
def capDotLinear (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    Obj J ((restriction J).obj N).toFunctor w →ₗ[k] N.obj w :=
  restrictionCounitLinear J N w ∘ₗ ((transformLinear hα ((restriction J).obj N) w) ^ n)

theorem unitDotColumn_total (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    SVec.toLinearMap ((unitDotColumn J hα M n).total w) = unitDotLinear J hα M n w := by
  rw [unitDotColumn, Superfunctor.comp_total, SVec.toLinearMap_comp,
    restriction_total, transform_power_total, unit_total]
  rfl

theorem capDotRow_total (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    SVec.toLinearMap ((capDotRow J hα N n).total w) = capDotLinear J hα N n w := by
  rw [capDotRow, Superfunctor.comp_total, SVec.toLinearMap_comp,
    transform_power_total, counit_total]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction
