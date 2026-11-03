import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixCaps
import OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixCoordinates

/-! # Prescribed finite content entries in the chosen coordinates

Brundan--Ellis (1.13)--(1.14), DeformedMatrixComparison (4), (5):
principal and dotted fields retain the canonical source/target parity
coordinates under the genuine selected content charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
namespace BalancedInduction
private def entryMateLinear
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M)) (t : C) :
    Obj A ((restriction A).obj M).toFunctor t →ₗ[k] Obj A M.toFunctor (A.obj t) := f.total t

private theorem entryMateLinear_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M)) (t : C)
    (x : Obj A ((restriction A).obj M).toFunctor t) :
    entryMateLinear A M f t x = f.total t x := rfl

private theorem entryMate_degree_eq
    {k C A B : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p q : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (e : p = q) (hp : IsSupernatural k p γ) (hq : IsSupernatural k q γ)
    (N : Superfunctor k A (SVec k)) (w : A) :
    orderedGridMateLinear J K hp N w = orderedGridMateLinear J K hq N w := by
  cases e
  rfl
section GenericFields
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
local instance contentEntryGenericPi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory
private theorem unit_some_total {p : ZMod 2}
    {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (N : Superfunctor k A (SVec k)) (m : ℕ) (r : Fin m) (w : A) :
    SVec.toLinearMap ((gridUnitMatrixEntry J K hγ hβ N m (some r)).total w) =
      unitDotLinear K hβ N r.val w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • p)).iso N).hom.total w) :=
  gridUnitMatrixEntry_some_total J K hγ hβ N m r w
end GenericFields

end BalancedInduction

private theorem compEquation_apply
    {k V W Z : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (o : V →ₗ[k] Z) (f : W →ₗ[k] Z) (z : V →ₗ[k] W)
    (h : o = f ∘ₗ z) (x : V) : o x = f (z x) := LinearMap.congr_fun h x

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local instance contentEntryCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) := supermodulePiSupercategory
local instance oldEntryCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory

/-- The same literal crossing has degree p, using p²=p. -/
theorem oldContentMatrixCross_supernatural :
    IsSupernatural k (D.parity i) (oldContentEqualCross D Sc cutoff ν i) := by
  simpa only [SKM.zmod2_mul_self] using oldContentEqualCross_supernatural D Sc cutoff ν i

private def oldEntryMateLinear
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (w : OldCategory D Sc cutoff) :
    Obj J ((restriction J).obj M).toFunctor w →ₗ[k] Obj J M.toFunctor ((J).obj w) :=
  BalancedInduction.entryMateLinear J M (matrixMateComponent D Sc cutoff i M) w

private theorem oldEntryMateLinear_apply
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (w : OldCategory D Sc cutoff)
    (x : Obj J ((restriction J).obj M).toFunctor w) :
    oldEntryMateLinear D Sc cutoff i M w x = (matrixMateComponent D Sc cutoff i M).total w x :=
  BalancedInduction.entryMateLinear_apply J M (matrixMateComponent D Sc cutoff i M) w x

private theorem oldUnit_none_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i M m none).total w) =
      oldEntryMateLinear D Sc cutoff i M w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
          (induced J ((restriction J).obj M))).hom.total w) := by
  let e := (SKM.homParityShiftDatum (k := k) (D.parity i)).iso (induced J ((restriction J).obj M))
  change SVec.toLinearMap ((e.hom ≫ matrixMateComponent D Sc cutoff i M).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp]
  rfl

private theorem oldUnit_some_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i M m (some r)).total w) =
      unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) M r.val w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total w) := by
  let e := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M
  change SVec.toLinearMap ((e.hom ≫ moduleUnitColumn D Sc cutoff i M r.val).total w) = _
  simp only [Superfunctor.comp_total, SVec.toLinearMap_comp, moduleUnitColumn_eq_unitDotColumn,
    unitDotColumn_total, e]

private theorem oldCap_none_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i M m none).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        ((restriction J).obj (induced J M))).inv.total w) ∘ₗ
          oldEntryMateLinear D Sc cutoff i M w := by
  let e := (SKM.homParityShiftDatum (k := k) (D.parity i)).iso ((restriction J).obj (induced J M))
  change SVec.toLinearMap ((matrixMateComponent D Sc cutoff i M ≫ e.inv).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp]
  rfl

private theorem oldCap_some_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i M m (some r)).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).inv.total w) ∘ₗ
        capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) M r.val w := by
  let e := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M
  change SVec.toLinearMap ((moduleCapRow D Sc cutoff i M r.val ≫ e.inv).total w) = _
  simp only [Superfunctor.comp_total, SVec.toLinearMap_comp, moduleCapRow_eq_capDotRow,
    capDotRow_total, e]

/-- Every given unit entry retains its canonical source coordinate under
the genuine selected content family and target charts. -/
theorem oldContentUnitEntry_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) (a : Option (Fin m))
    (x : (gridUnitMatrixFamily J₀ (D.parity i) N m a).obj t) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap
      (SVec.toLinearMap ((gridUnitMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m a).total t) x) =
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i (induced Q₁ N) m a).total t.obj)
      ((oldContentUnitSlotEquiv D Sc cutoff ν i N m t a).toLinearMap x) := by
  cases a with
  | none =>
    have hA := compEquation_apply _ _ _ (gridUnitMatrixEntry_none_total J₀ J₁
      (oldContentMatrixCross_supernatural D Sc cutoff ν i)
      (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m t) x
    have hO := compEquation_apply _ _ _ (oldUnit_none_total D Sc cutoff i (induced Q₁ N) m t.obj)
      ((oldContentUnitSlotEquiv D Sc cutoff ν i N m t none).toLinearMap x)
    have hz := shiftedModuleValueLinearEquiv_hom_coordinate
      (induced J₀ ((restriction J₀).obj N)) (induced J ((restriction J).obj (induced Q₁ N)))
      t t.obj (oldContentEFLinearEquiv D Sc cutoff ν i N t) (D.parity i) x
    have hB := oldContentMatrixCharts_mate D Sc cutoff ν i N t
      (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        (induced J₀ ((restriction J₀).obj N))).hom.total t x)
    simp only [SKM.zmod2_mul_self] at hB
    have hm := oldEntryMateLinear_apply D Sc cutoff i (induced Q₁ N) t.obj
      ((oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap
        (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
          (induced J₀ ((restriction J₀).obj N))).hom.total t x))
    have hPlain := hB.trans hm.symm
    have hCoord := congrArg (oldEntryMateLinear D Sc cutoff i (induced Q₁ N) t.obj) hz
    have hLeft := congrArg (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap hA
    have h₁ := hCoord.symm.trans hO.symm
    have h₂ := hPlain.trans h₁
    have hFinal := hLeft.trans h₂
    exact hFinal
  | some r =>
    have hA := compEquation_apply _ _ _ (BalancedInduction.unit_some_total J₀ J₁
      (oldContentMatrixCross_supernatural D Sc cutoff ν i)
      (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m r t) x
    have hO := compEquation_apply _ _ _ (oldUnit_some_total D Sc cutoff i (induced Q₁ N) m r t.obj)
      ((oldContentUnitSlotEquiv D Sc cutoff ν i N m t (some r)).toLinearMap x)
    have hz := shiftedModuleValueLinearEquiv_hom_coordinate N (induced Q₁ N)
      t t.obj (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i) x
    have hBase := oldContentFELinearEquiv_unitDot D Sc cutoff ν i N t r.val
      (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso N).hom.total t x)
    have hCoord := congrArg (unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i)
      (induced Q₁ N) r.val t.obj) hz
    have hLeft := congrArg (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap hA
    have h₁ := hCoord.symm.trans hO.symm
    have h₂ := hBase.trans h₁
    have hFinal := hLeft.trans h₂
    exact hFinal

end OddMath.QuiverHecke.ELVOld
