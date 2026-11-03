import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixFamilyCharts

/-! # The prescribed scalar finite matrix entries under the selected charts

DeformedMatrixComparison (4), (5) requires the actual crossing-derived mate
and dotted unit/cap fields, with the fixed canonical parity coordinates.
This module compares these entries before assembling the two matrices.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u

section GenericOperators
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

private theorem matrixMate_degree_eq {p q : ZMod 2}
    {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (e : p = q)
    (hp : IsSupernatural k p γ) (hq : IsSupernatural k q γ)
    (N : Superfunctor k A (SVec k)) (w : A) :
    orderedGridMateLinear J K hp N w = orderedGridMateLinear J K hq N w := by
  cases e
  rfl

private theorem matrixMate_endpoint_refl {p : ZMod 2}
    {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
    (N : Superfunctor k A (SVec k)) (w : A) :
    endpointGridMateLinear J K hγ N w (K.obj w) rfl = orderedGridMateLinear J K hγ N w := by
  unfold endpointGridMateLinear
  rw [eqToHom_refl, postcompose_id, LinearMap.id_comp]

private theorem matrixUnit_endpoint_refl {p : ZMod 2}
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    endpointUnitDotLinear K hβ N n w (K.obj w) rfl = unitDotLinear K hβ N n w := by
  apply LinearMap.ext
  intro b
  exact (endpointUnitDotLinear_refl_apply K hβ N n w b).trans
    (unitDotLinear_apply K hβ N n w b).symm

local instance entryFieldModulePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory

private theorem matrixUnit_field_some_total {p : ZMod 2}
    {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (N : Superfunctor k A (SVec k)) (m : ℕ) (r : Fin m) (w : A) :
    SVec.toLinearMap ((gridUnitMatrixEntry J K hγ hβ N m (some r)).total w) =
      unitDotLinear K hβ N r.val w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • p)).iso N).hom.total w) :=
  gridUnitMatrixEntry_some_total J K hγ hβ N m r w

private theorem matrixCap_field_some_total {p : ZMod 2}
    {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
    {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (N : Superfunctor k A (SVec k)) (m : ℕ) (r : Fin m) (w : A) :
    SVec.toLinearMap ((gridCapMatrixEntry J K hγ hα N m (some r)).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • p)).iso N).inv.total w) ∘ₗ
        capDotLinear J hα N r.val w := gridCapMatrixEntry_some_total J K hγ hα N m r w

end GenericOperators

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

private theorem matrixSquare_reencode
    {k V W X Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (c c₀ : W →ₗ[k] Y) (f f₀ : V →ₗ[k] W) (g g₀ : X →ₗ[k] Y) (d d₀ : V →ₗ[k] X)
    (hc : c = c₀) (hf : f = f₀) (hg : g = g₀) (hd : d = d₀)
    (h : c₀ ∘ₗ f₀ = g₀ ∘ₗ d₀) : c ∘ₗ f = g ∘ₗ d := by
  rw [hc, hf, hg, hd]
  exact h

private theorem matrixUnit_plain_reencode
    {k V W Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid Y] [Module k Y]
    (c c₀ : W →ₗ[k] Y) (f : V →ₗ[k] W) (g g₀ : V →ₗ[k] Y) (v : V →ₗ[k] V)
    (hc : c = c₀) (hg : g₀ = g) (hv : ∀ b, v b = b) (h : c₀ ∘ₗ f = g₀) :
    c ∘ₗ f = g ∘ₗ v := by
  rw [hc]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun h b).trans
    ((LinearMap.congr_fun hg b).trans (congrArg g (hv b)).symm)

private theorem matrixCap_plain_reencode
    {k V W X Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (e : W ≃ₗ[k] Y) (a : V →ₗ[k] W) (b : X →ₗ[k] Y)
    (c c₀ : V →ₗ[k] X) (v : Y →ₗ[k] W)
    (hc : c = c₀) (hv : v = e.symm.toLinearMap) (h : v ∘ₗ b ∘ₗ c₀ = a) :
    e.toLinearMap ∘ₗ a = b ∘ₗ c := by
  rw [hc]
  rw [hv] at h
  apply LinearMap.ext
  intro x
  exact (congrArg e (LinearMap.congr_fun h x)).symm.trans (e.apply_symm_apply (b (c₀ x)))

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)

/-- The literal old same-colour crossing has degree p, since p²=p in ZMod 2. -/
theorem probeMatrixOldCross_supernatural :
    IsSupernatural k (D.parity i) (probeOldContentEqualCross D Sc m ν i) := by
  simpa only [SKM.zmod2_mul_self] using probeOldContentEqualCross_supernatural D Sc m ν i

/-- The ordinary crossing has the same normalized degree and unchanged coefficient. -/
theorem probeMatrixOrdinaryCross_supernatural :
    IsSupernatural k (D.parity i) (probeOrdinaryEqualCross D Sc m ν i) := by
  simpa only [SKM.zmod2_mul_self] using probeOrdinaryEqualCross_supernatural D Sc m ν i

variable
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "K" => ELVOld.oldContentAppend D Sc (probeCutoff D m) (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
local notation "RN" => Functor.obj (restriction J) N
local notation "hR" => probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
local notation "cR" => eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)

/-- The genuine E/F and F/E charts intertwine the prescribed ordinary mate,
with the same crossing and its normalized degree. -/
theorem probeMatrixCharts_mate
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w).toLinearMap ∘ₗ
        orderedGridMateLinear J K (probeMatrixOldCross_supernatural D Sc m ν i) N w =
      orderedGridMateLinear T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i) O ((U).obj w) ∘ₗ
        (probeMatrixSourceLinearEquiv D Sc m ν i N hN w).toLinearMap := by
  have hOld := matrixMate_degree_eq J K (SKM.zmod2_mul_self (D.parity i))
    (probeOldContentEqualCross_supernatural D Sc m ν i) (probeMatrixOldCross_supernatural D Sc m ν i) N w
  have hNew₀ := matrixMate_endpoint_refl T S
    (probeOrdinaryEqualCross_supernatural D Sc m ν i) O ((U).obj w)
  have hNew₁ := matrixMate_degree_eq T S (SKM.zmod2_mul_self (D.parity i))
    (probeOrdinaryEqualCross_supernatural D Sc m ν i)
    (probeMatrixOrdinaryCross_supernatural D Sc m ν i) O ((U).obj w)
  have hNew := hNew₀.trans hNew₁
  exact matrixSquare_reencode _ _ _ _ _ _ _ _
    (probeMatrixTargetLinearEquiv_hom D Sc m ν i N hN w) hOld.symm hNew.symm
    (probeMatrixSourceLinearEquiv_hom D Sc m ν i N hN w)
    (probeAppendOrdinaryModuleIso_mate D Sc m ν i N hN w)

/-- The selected target/value charts intertwine every actual unshifted
unit/dot column of the finite matrix. -/
theorem probeMatrixCharts_unitDotColumn
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (n : ℕ) :
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w).toLinearMap ∘ₗ
        unitDotLinear K (probeOldContentAppendDot_supernatural D Sc m (i :: ν) i) N n w =
      unitDotLinear S (probeOrdinaryAppendDot_supernatural D Sc m (i :: ν) i) O n ((U).obj w) ∘ₗ
        (probeMatrixValueLinearEquiv D Sc m ν i N hN w).toLinearMap := by
  have h := probeAppendComparisonLinear_unitDotColumn D Sc m (i :: ν) N hN i w n
  have hEnd := matrixUnit_endpoint_refl S (probeOrdinaryAppendDot_supernatural D Sc m (i :: ν) i)
    O n ((U).obj w)
  exact matrixUnit_plain_reencode _ _ _ _ _ _
    (probeMatrixTargetLinearEquiv_hom D Sc m ν i N hN w) hEnd
    (probeMatrixValueLinearEquiv_apply D Sc m ν i N hN w) h

/-- The selected source/value charts intertwine every actual unshifted
signed dot/counit row of the finite matrix. -/
theorem probeMatrixCharts_capDotRow
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (n : ℕ) :
    (probeMatrixValueLinearEquiv D Sc m ν i N hN w).toLinearMap ∘ₗ
        capDotLinear J (probeOldContentAppendDot_supernatural D Sc m ν i) N n w =
      capDotLinear T (probeOrdinaryAppendDot_supernatural D Sc m ν i) O n ((U).obj w) ∘ₗ
        (probeMatrixSourceLinearEquiv D Sc m ν i N hN w).toLinearMap := by
  have h := probeMappedAppendLinear_capDotRow D Sc m ν i N hN w n
  exact matrixCap_plain_reencode (probeMatrixValueLinearEquiv D Sc m ν i N hN w) _ _ _ _ _
    (probeMatrixSourceLinearEquiv_hom D Sc m ν i N hN w) rfl h

/-- The actual first unit-matrix field commutes with its canonical shifted
E/F source chart and the selected F/E target chart. -/
theorem probeMatrixCharts_unitEntry_none
    (b : ℕ) (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w).toLinearMap ∘ₗ
        SVec.toLinearMap ((gridUnitMatrixEntry J K (probeMatrixOldCross_supernatural D Sc m ν i)
          (probeOldContentAppendDot_supernatural D Sc m (i :: ν) i) N b none).total w) =
      SVec.toLinearMap ((gridUnitMatrixEntry T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
          (probeOrdinaryAppendDot_supernatural D Sc m (i :: ν) i) O b none).total ((U).obj w)) ∘ₗ
        (probeUnitMatrixSlotLinearEquiv D Sc m ν i N hN b w none).toLinearMap := by
  have h := probeMatrixCharts_mate D Sc m ν i N hN w
  have hz := matrixPoint_source_coordinate (induced J RN) (induced T ((restriction T).obj O))
    w ((U).obj w) (probeMatrixSourceLinearEquiv D Sc m ν i N hN w) (D.parity i)
  have ho := gridUnitMatrixEntry_none_total J K (probeMatrixOldCross_supernatural D Sc m ν i)
    (probeOldContentAppendDot_supernatural D Sc m (i :: ν) i) N b w
  have hn := gridUnitMatrixEntry_none_total T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
    (probeOrdinaryAppendDot_supernatural D Sc m (i :: ν) i) O b ((U).obj w)
  exact matrixColumn_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- The actual first cap-matrix field commutes with its canonical shifted
F/E target chart and the selected E/F source chart. -/
theorem probeMatrixCharts_capEntry_none
    (b : ℕ) (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeCapMatrixSlotLinearEquiv D Sc m ν i N hN b w none).toLinearMap ∘ₗ
        SVec.toLinearMap ((gridCapMatrixEntry J K (probeMatrixOldCross_supernatural D Sc m ν i)
          (probeOldContentAppendDot_supernatural D Sc m ν i) N b none).total w) =
      SVec.toLinearMap ((gridCapMatrixEntry T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
          (probeOrdinaryAppendDot_supernatural D Sc m ν i) O b none).total ((U).obj w)) ∘ₗ
        (probeMatrixSourceLinearEquiv D Sc m ν i N hN w).toLinearMap := by
  have h := probeMatrixCharts_mate D Sc m ν i N hN w
  have hz := matrixPoint_target_coordinate ((restriction K).obj (induced K N))
    ((restriction S).obj (induced S O)) w ((U).obj w)
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w) (D.parity i)
  have ho := gridCapMatrixEntry_none_total J K (probeMatrixOldCross_supernatural D Sc m ν i)
    (probeOldContentAppendDot_supernatural D Sc m ν i) N b w
  have hn := gridCapMatrixEntry_none_total T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
    (probeOrdinaryAppendDot_supernatural D Sc m ν i) O b ((U).obj w)
  exact matrixRow_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every actual dotted unit field commutes with the same canonical source
slot and selected F/E target charts. -/
theorem probeMatrixCharts_unitEntry_some
    (b : ℕ) (r : Fin b) (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w).toLinearMap ∘ₗ
        SVec.toLinearMap ((gridUnitMatrixEntry J K (probeMatrixOldCross_supernatural D Sc m ν i)
          (probeOldContentAppendDot_supernatural D Sc m (i :: ν) i) N b (some r)).total w) =
      SVec.toLinearMap ((gridUnitMatrixEntry T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
          (probeOrdinaryAppendDot_supernatural D Sc m (i :: ν) i) O b (some r)).total ((U).obj w)) ∘ₗ
        (probeUnitMatrixSlotLinearEquiv D Sc m ν i N hN b w (some r)).toLinearMap := by
  have h := probeMatrixCharts_unitDotColumn D Sc m ν i N hN w r.val
  have hz := matrixPoint_source_coordinate N O w ((U).obj w)
    (probeMatrixValueLinearEquiv D Sc m ν i N hN w) (r.val • D.parity i)
  have ho := matrixUnit_field_some_total J K (probeMatrixOldCross_supernatural D Sc m ν i)
    (probeOldContentAppendDot_supernatural D Sc m (i :: ν) i) N b r w
  have hn := matrixUnit_field_some_total T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
    (probeOrdinaryAppendDot_supernatural D Sc m (i :: ν) i) O b r ((U).obj w)
  exact matrixColumn_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every actual dotted cap field commutes with the same canonical target
slot and selected E/F source charts. -/
theorem probeMatrixCharts_capEntry_some
    (b : ℕ) (r : Fin b) (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeCapMatrixSlotLinearEquiv D Sc m ν i N hN b w (some r)).toLinearMap ∘ₗ
        SVec.toLinearMap ((gridCapMatrixEntry J K (probeMatrixOldCross_supernatural D Sc m ν i)
          (probeOldContentAppendDot_supernatural D Sc m ν i) N b (some r)).total w) =
      SVec.toLinearMap ((gridCapMatrixEntry T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
          (probeOrdinaryAppendDot_supernatural D Sc m ν i) O b (some r)).total ((U).obj w)) ∘ₗ
        (probeMatrixSourceLinearEquiv D Sc m ν i N hN w).toLinearMap := by
  have h := probeMatrixCharts_capDotRow D Sc m ν i N hN w r.val
  have hz := matrixPoint_target_coordinate N O w ((U).obj w)
    (probeMatrixValueLinearEquiv D Sc m ν i N hN w) (r.val • D.parity i)
  have ho := matrixCap_field_some_total J K (probeMatrixOldCross_supernatural D Sc m ν i)
    (probeOldContentAppendDot_supernatural D Sc m ν i) N b r w
  have hn := matrixCap_field_some_total T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
    (probeOrdinaryAppendDot_supernatural D Sc m ν i) O b r ((U).obj w)
  exact matrixRow_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- All fields of the prescribed scalar unit matrix commute with their
actual chosen charts, including the crossing-derived first field. -/
theorem probeMatrixCharts_unitEntry
    (b : ℕ) (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (a : Option (Fin b)) :
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w).toLinearMap ∘ₗ
        SVec.toLinearMap ((gridUnitMatrixEntry J K (probeMatrixOldCross_supernatural D Sc m ν i)
          (probeOldContentAppendDot_supernatural D Sc m (i :: ν) i) N b a).total w) =
      SVec.toLinearMap ((gridUnitMatrixEntry T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
          (probeOrdinaryAppendDot_supernatural D Sc m (i :: ν) i) O b a).total ((U).obj w)) ∘ₗ
        (probeUnitMatrixSlotLinearEquiv D Sc m ν i N hN b w a).toLinearMap := by
  cases a with
  | none => exact probeMatrixCharts_unitEntry_none D Sc m ν i N hN b w
  | some r => exact probeMatrixCharts_unitEntry_some D Sc m ν i N hN b r w

/-- All fields of the prescribed scalar cap matrix commute with their
actual chosen charts, including the crossing-derived first field. -/
theorem probeMatrixCharts_capEntry
    (b : ℕ) (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (a : Option (Fin b)) :
    (probeCapMatrixSlotLinearEquiv D Sc m ν i N hN b w a).toLinearMap ∘ₗ
        SVec.toLinearMap ((gridCapMatrixEntry J K (probeMatrixOldCross_supernatural D Sc m ν i)
          (probeOldContentAppendDot_supernatural D Sc m ν i) N b a).total w) =
      SVec.toLinearMap ((gridCapMatrixEntry T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
          (probeOrdinaryAppendDot_supernatural D Sc m ν i) O b a).total ((U).obj w)) ∘ₗ
        (probeMatrixSourceLinearEquiv D Sc m ν i N hN w).toLinearMap := by
  cases a with
  | none => exact probeMatrixCharts_capEntry_none D Sc m ν i N hN b w
  | some r => exact probeMatrixCharts_capEntry_some D Sc m ν i N hN b r w

end OddMath.QuiverHecke
