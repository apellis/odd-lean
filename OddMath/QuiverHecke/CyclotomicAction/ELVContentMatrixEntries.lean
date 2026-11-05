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

section GenericCoordinates
variable {k A B : Type u} [CommRing k]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (M : Superfunctor k A (SVec k)) (N : Superfunctor k B (SVec k))
  (w : A) (v : B) (e : M.obj w ≃ₗ[k] N.obj v)
local instance entryCoordinateSourcePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory
local instance entryCoordinateTargetPi : PiSupercategory k (Superfunctor k B (SVec k)) :=
  supermodulePiSupercategory

private theorem matrixPoint_source_coordinate (q : ZMod 2) :
    SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).hom.total v) ∘ₗ
        (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap =
      e.toLinearMap ∘ₗ SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).hom.total w) := by
  apply LinearMap.ext
  intro b
  exact shiftedModuleValueLinearEquiv_hom_coordinate M N w v e q b

private theorem matrixPoint_target_coordinate (q : ZMod 2) :
    (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).inv.total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).inv.total v) ∘ₗ e.toLinearMap := by
  apply LinearMap.ext
  intro b
  exact shiftedModuleValueLinearEquiv_inv_coordinate M N w v e q b

end GenericCoordinates

private theorem matrixColumn_decorate
    {k V W X Y A B : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (z : A →ₗ[k] V) (z' : B →ₗ[k] X) (s : A →ₗ[k] B)
    (o : A →ₗ[k] W) (n : B →ₗ[k] Y)
    (h : c ∘ₗ f = g ∘ₗ d) (hz : z' ∘ₗ s = d ∘ₗ z)
    (ho : o = f ∘ₗ z) (hn : n = g ∘ₗ z') : c ∘ₗ o = n ∘ₗ s := by
  rw [ho, hn]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun h (z b)).trans (congrArg g (LinearMap.congr_fun hz b).symm)

private theorem matrixRow_decorate
    {k V W X Y A B : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (z : W →ₗ[k] A) (z' : Y →ₗ[k] B) (s : A →ₗ[k] B)
    (o : V →ₗ[k] A) (n : X →ₗ[k] B)
    (h : c ∘ₗ f = g ∘ₗ d) (hz : s ∘ₗ z = z' ∘ₗ c)
    (ho : o = z ∘ₗ f) (hn : n = z' ∘ₗ g) : s ∘ₗ o = n ∘ₗ d := by
  rw [ho, hn]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun hz (f b)).trans (congrArg z' (LinearMap.congr_fun h b))

private theorem square_degree_reencode
    {k V W X Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (c : W →ₗ[k] Y) (f f' : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (he : f = f') (h : c ∘ₗ f = g ∘ₗ d) : c ∘ₗ f' = g ∘ₗ d := by
  rw [← he]
  exact h

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

private theorem oldUnit_none_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i M m none).total w) =
      oldMatrixMateLinear D Sc cutoff i M w ∘ₗ
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
          oldMatrixMateLinear D Sc cutoff i M w := by
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

/-- The chosen charts intertwine the unshifted principal entry. -/
private theorem oldContentEntry_mate
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      orderedGridMateLinear J₀ J₁ (oldContentMatrixCross_supernatural D Sc cutoff ν i) N t =
    oldMatrixMateLinear D Sc cutoff i (induced Q₁ N) t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  have he := BalancedInduction.entryMate_degree_eq J₀ J₁
    (SKM.zmod2_mul_self (D.parity i))
    (oldContentEqualCross_supernatural D Sc cutoff ν i)
    (oldContentMatrixCross_supernatural D Sc cutoff ν i) N t
  exact square_degree_reencode _ _ _ _ _ he
    (oldContentMatrixCharts_mate_comp D Sc cutoff ν i N t)

/-- The first prescribed unit field retains the canonical source coordinate. -/
theorem oldContentUnitEntry_none_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridUnitMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m none).total t) =
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i (induced Q₁ N) m none).total t.obj) ∘ₗ
      (oldContentUnitSlotEquiv D Sc cutoff ν i N m t none).toLinearMap := by
  have h := oldContentEntry_mate D Sc cutoff ν i N t
  have hz := matrixPoint_source_coordinate
    (induced J₀ ((restriction J₀).obj N)) (induced J ((restriction J).obj (induced Q₁ N)))
    t t.obj (oldContentEFLinearEquiv D Sc cutoff ν i N t) (D.parity i)
  have ho := gridUnitMatrixEntry_none_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m t
  have hn := oldUnit_none_total D Sc cutoff i (induced Q₁ N) m t.obj
  exact matrixColumn_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every prescribed dotted unit field retains its canonical source coordinate. -/
theorem oldContentUnitEntry_some_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) (r : Fin m) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridUnitMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m (some r)).total t) =
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i (induced Q₁ N) m (some r)).total t.obj) ∘ₗ
      (oldContentUnitSlotEquiv D Sc cutoff ν i N m t (some r)).toLinearMap := by
  have h : (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      unitDotLinear J₁ (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N r.val t =
    unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) (induced Q₁ N) r.val t.obj ∘ₗ
      (oldContentValueLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
    apply LinearMap.ext
    intro b
    exact oldContentFELinearEquiv_unitDot D Sc cutoff ν i N t r.val b
  have hz := matrixPoint_source_coordinate N (induced Q₁ N)
    t t.obj (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)
  have ho := BalancedInduction.unit_some_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m r t
  have hn := oldUnit_some_total D Sc cutoff i (induced Q₁ N) m r t.obj
  exact matrixColumn_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- The principal cap field retains the canonical target coordinate. -/
theorem oldContentCapEntry_none_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentCapSlotEquiv D Sc cutoff ν i N m t none).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridCapMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff ν i) N m none).total t) =
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i (induced Q₁ N) m none).total t.obj) ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  have h := oldContentEntry_mate D Sc cutoff ν i N t
  have hz := matrixPoint_target_coordinate
    ((restriction J₁).obj (induced J₁ N)) ((restriction J).obj (induced J (induced Q₁ N)))
    t t.obj (oldContentFELinearEquiv D Sc cutoff ν i N t) (D.parity i)
  have ho := gridCapMatrixEntry_none_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff ν i) N m t
  have hn := oldCap_none_total D Sc cutoff i (induced Q₁ N) m t.obj
  exact matrixRow_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every dotted cap field retains the canonical target coordinate. -/
theorem oldContentCapEntry_some_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) (r : Fin m) :
    (oldContentCapSlotEquiv D Sc cutoff ν i N m t (some r)).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridCapMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff ν i) N m (some r)).total t) =
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i (induced Q₁ N) m (some r)).total t.obj) ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  have h : (oldContentValueLinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      capDotLinear J₀ (oldContentAppendDot_supernatural D Sc cutoff ν i) N r.val t =
    capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) (induced Q₁ N) r.val t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
    apply LinearMap.ext
    intro b
    exact oldContentEFLinearEquiv_capDot D Sc cutoff ν i N t r.val b
  have hz := matrixPoint_target_coordinate N (induced Q₁ N)
    t t.obj (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)
  have ho := gridCapMatrixEntry_some_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff ν i) N m r t
  have hn := oldCap_some_total D Sc cutoff i (induced Q₁ N) m r t.obj
  exact matrixRow_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

end OddMath.QuiverHecke.ELVOld
