import OddMath.QuiverHecke.CyclotomicAction.ELVProbeShiftedCapComparison

/-! # Prescribed unit columns with their canonical parity sources

DeformedMatrixComparison (1), (4) uses the given unit/dot columns without
column rescaling. The existing canonical source parity coordinate is kept
as a module map, then transported through the scalar restriction bridge.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

section ShiftedColumns
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
local instance shiftedUnitColumnsModulePi : PiSupercategory k (Superfunctor k C (SVec k)) := supermodulePiSupercategory

/-- The actual unit/dot column with its canonical shifted source. -/
def shiftedUnitDotColumn (M : Superfunctor k C (SVec k)) (n : ℕ) :
    (SKM.homParityShift (k := k) (n • p)).obj M ⟶
      (restriction J).obj ((induction J).obj M) :=
  ((SKM.homParityShiftDatum (k := k) (n • p)).iso M).hom ≫ unitDotColumn J hα M n

theorem shiftedUnitDotColumn_mem (M : Superfunctor k C (SVec k)) (n : ℕ) :
    shiftedUnitDotColumn J hα M n ∈ parity (R := k) _ _ 0 := by
  simpa only [shiftedUnitDotColumn, SKM.zmod2_add_self] using comp_mem
    ((SKM.homParityShiftDatum (k := k) (n • p)).hom_mem M) (unitDotColumn_mem J hα M n)

/-- Literal component of the actual shifted column. -/
def shiftedUnitDotLinear (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    ((SKM.homParityShift (k := k) (n • p)).obj M).obj w →ₗ[k] Obj J M.toFunctor (J.obj w) :=
  unitDotLinear J hα M n w ∘ₗ
    SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (n • p)).iso M).hom.total w)

theorem shiftedUnitDotColumn_total (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    SVec.toLinearMap ((shiftedUnitDotColumn J hα M n).total w) =
      shiftedUnitDotLinear J hα M n w := by
  rw [shiftedUnitDotColumn, Superfunctor.comp_total, SVec.toLinearMap_comp, unitDotColumn_total]
  rfl

/-- Evaluate a given unit/dot column before specializing its coend. -/
theorem unitDotLinear_apply (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) (b : M.obj w) :
    unitDotLinear J hα M n w b = ((transformLinear hα M (J.obj w)) ^ n) (unit J M.toFunctor w b) := rfl

/-- The canonical reflexive endpoint transport changes no unit/dot column. -/
theorem endpointUnitDotLinear_refl_apply (M : Superfunctor k C (SVec k))
    (n : ℕ) (w : C) (b : M.obj w) :
    endpointUnitDotLinear J hα M n w (J.obj w) rfl b =
      ((transformLinear hα M (J.obj w)) ^ n) (unit J M.toFunctor w b) := by
  simp only [endpointUnitDotLinear, eqToHom_refl, postcompose_id, LinearMap.comp_apply,
    LinearMap.id_apply]

private theorem unitDotPowerTransport (M : Superfunctor k C (SVec k)) (w : C)
    {W : Type u} [AddCommMonoid W] [Module k W]
    (c : Obj J M.toFunctor (J.obj w) →ₗ[k] W) (g : Module.End k W)
    (v : M.obj w →ₗ[k] W)
    (hD : c ∘ₗ transformLinear hα M (J.obj w) = g ∘ₗ c)
    (hU : c ∘ₗ unit J M.toFunctor w = v) (n : ℕ) :
    c ∘ₗ unitDotLinear J hα M n w = (g ^ n) ∘ₗ v := by
  ext b
  have hp := intertwine_pow_apply c (transformLinear hα M (J.obj w)) g
    (fun x => LinearMap.congr_fun hD x) n (unit J M.toFunctor w b)
  exact hp.trans (congrArg (g ^ n) (LinearMap.congr_fun hU b))

private theorem endpointUnitDotLinear_refl (M : Superfunctor k C (SVec k))
    (n : ℕ) (w : C) : endpointUnitDotLinear J hα M n w (J.obj w) rfl =
      ((transformLinear hα M (J.obj w)) ^ n) ∘ₗ unit J M.toFunctor w := by
  ext b
  exact endpointUnitDotLinear_refl_apply J hα M n w b

end ShiftedColumns

section Coordinates
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (Q : C ⥤ D) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (M : Superfunctor k D (SVec k)) (N : Superfunctor k C (SVec k))
  (e : (restriction Q).obj M ≅ N)
local instance shiftedUnitCoordinateSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) := supermodulePiSupercategory
local instance shiftedUnitCoordinateTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) := supermodulePiSupercategory

end Coordinates

section Comparison
variable {k C A D B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (T : D ⥤ B) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (Q : C ⥤ D) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)
  (M : Superfunctor k D (SVec k)) (N : Superfunctor k C (SVec k))
  (e : (restriction Q).obj M ≅ N)
local instance shiftedUnitComparisonSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) := supermodulePiSupercategory
local instance shiftedUnitComparisonTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) := supermodulePiSupercategory

end Comparison

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
private def unitDotCoefficient
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s}
    (s : C) (t : A) (g : J.obj s ⟶ t) : J.obj s ⟶ t := α s ≫ twist k p g

private theorem unitCoendHom_ext
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A} {f g : Obj J M w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : M.obj s), f (tensor J M s a b) = g (tensor J M s a b)) :
    f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

private theorem unitTensorSource_congr
    {k A B : Type u} [CommRing k] [Category.{u} A] [Category.{u} B]
    [Preadditive B] [Linear k B] (K : A ⥤ B) (M : A ⥤ SVec k)
    (w : B) (v v' : A) (e : v = v') (g : K.obj v ⟶ w) (g' : K.obj v' ⟶ w)
    (b : M.obj v) (b' : M.obj v') (hg : HEq g g') (hb : HEq b b') :
    tensor K M v g b = tensor K M v' g' b' := by
  cases e
  cases hg
  cases hb
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N) (i : I)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν N hN

/-- The original selected append map intertwines the given signed dots. -/
theorem probeAppendComparisonLinear_dot
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    probeAppendComparisonLinear D Sc m ν N hN i w ∘ₗ
        probeOldContentInductionDot D Sc m ν i N w =
      transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i) O ((U).obj w) ∘ₗ
        probeAppendComparisonLinear D Sc m ν N hN i w := by
  apply unitCoendHom_ext J N.toFunctor
  intro s g b
  have ho := probeOldContentInductionDot_tensor D Sc m ν i N s w g b
  have hq := probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN i s w
    (probeOldContentAppendDot D Sc m ν i s ≫ twist k (D.parity i) g) b
  have hl := (congrArg (probeAppendComparisonLinear D Sc m ν N hN i w) ho).trans hq
  have hs := probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN i s w g b
  have ht := transformLinear_tensor (probeOrdinaryAppendDot_supernatural D Sc m ν i) O
    ((U).obj w) ((Q).obj s) ((U).map g) b
  have hr := (congrArg (transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i)
    O ((U).obj w)) hs).trans ht
  let aNew := unitDotCoefficient (k := k) T (p := D.parity i)
    (α := probeOrdinaryAppendDot D Sc m ν i) ((Q).obj s) ((U).obj w) ((U).map g)
  have ha : HEq ((U).map (probeOldContentAppendDot D Sc m ν i s ≫
      twist k (D.parity i) g)) aNew := by
    apply heq_of_eq
    dsimp only [aNew, unitDotCoefficient, probeOldContentAppendDot]
    rw [(U).map_comp, map_twist, probeOrdinaryAppendDot_old D Sc m ν i s]
    rfl
  have he := unitTensorSource_congr T (O).toFunctor ((U).obj w) ((Q).obj s) ((Q).obj s)
    rfl _ aNew b b ha HEq.rfl
  exact hl.trans (he.trans hr.symm)

/-- The selected append chart transports every actual unit/dot column, with
its canonical output-object identification. -/
theorem probeAppendComparisonLinear_unitDotColumn
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (n : ℕ) :
    probeAppendComparisonLinear D Sc m ν N hN i ((J).obj w) ∘ₗ
        unitDotLinear J (probeOldContentAppendDot_supernatural D Sc m ν i) N n w =
      endpointUnitDotLinear T (probeOrdinaryAppendDot_supernatural D Sc m ν i) O n
        ((Q).obj w) ((U).obj ((J).obj w)) rfl := by
  have hU : probeAppendComparisonLinear D Sc m ν N hN i ((J).obj w) ∘ₗ
      unit J N.toFunctor w = unit T (O).toFunctor ((Q).obj w) := by
    ext b
    exact probeAppendOrdinaryModuleIso_hom_unit D Sc m ν N hN i w b
  have h := unitDotPowerTransport J (probeOldContentAppendDot_supernatural D Sc m ν i) N w
    (probeAppendComparisonLinear D Sc m ν N hN i ((J).obj w))
    (transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i) O ((U).obj ((J).obj w)))
    (unit T (O).toFunctor ((Q).obj w))
    (probeAppendComparisonLinear_dot D Sc m ν N hN i ((J).obj w)) hU n
  have he := endpointUnitDotLinear_refl T (probeOrdinaryAppendDot_supernatural D Sc m ν i)
    O n ((Q).obj w)
  exact h.trans he.symm

local notation "e" => eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)
local instance scalarShiftedUnitOldPi : PiSupercategory k
    (Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k)) :=
  supermodulePiSupercategory
local instance scalarShiftedUnitOrdinaryPi : PiSupercategory k
    (Superfunctor k (OrdinaryContentCategory D Sc
      (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k)) :=
  supermodulePiSupercategory

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance unitMatrixEntryComparisonPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
