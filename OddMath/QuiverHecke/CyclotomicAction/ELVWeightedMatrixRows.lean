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

/-- The given homogeneous dot, with its module endomorphism endpoint fixed. -/
def dotEnd (M : Superfunctor k C (SVec k)) : End ((induction J).obj M) :=
  transformComponent hα M

theorem dotEnd_mem (M : Superfunctor k C (SVec k)) :
    dotEnd J hα M ∈ parity (R := k) _ _ p := by
  change transformComponent hα M ∈ parity (R := k) (induced J M) (induced J M) p
  exact transformComponent_mem hα M

/-- The actual ordinary unit followed by the restricted dot power. -/
def unitDotColumn (M : Superfunctor k C (SVec k)) (n : ℕ) :
    M ⟶ (restriction J).obj ((induction J).obj M) :=
  (adjunction J).unit.app M ≫ (restriction J).map ((dotEnd J hα M) ^ n)

/-- The actual dot power followed by the ordinary counit. -/
def capDotRow (N : Superfunctor k A (SVec k)) (n : ℕ) :
    (induction J).obj ((restriction J).obj N) ⟶ N :=
  ((dotEnd J hα ((restriction J).obj N)) ^ n) ≫ (adjunction J).counit.app N

theorem transform_power_mem (M : Superfunctor k C (SVec k)) (n : ℕ) :
    (dotEnd J hα M) ^ n ∈ parity (R := k) _ _ (n • p) := by
  induction n with
  | zero =>
    simp only [pow_zero, End.one_def, zero_nsmul]
    exact id_mem _
  | succ n ih =>
    rw [pow_succ, End.mul_def]
    simpa only [succ_nsmul, add_comm] using comp_mem (dotEnd_mem J hα M) ih

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
    SVec.toLinearMap ((dotEnd J hα M).total w) = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [dotEnd, SuperNatTrans.total, transformComponent_app, ite_true, ite_false,
      zero_ne_one, one_ne_zero, zero_add, add_zero, SVec.toLinearMap]

private theorem transform_power_total (M : Superfunctor k C (SVec k)) (w : A) (n : ℕ) :
    SVec.toLinearMap (((dotEnd J hα M) ^ n).total w) = (transformLinear hα M w) ^ n := by
  have h := total_power (dotEnd J hα M) w n
  rw [transform_total] at h
  exact h

private theorem restriction_total {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) :
    ((restriction J).map f).total w = f.total (J.obj w) := rfl

private theorem unit_total (M : Superfunctor k C (SVec k)) (w : C) :
    SVec.toLinearMap (((adjunction J).unit.app M).total w) = unit J M.toFunctor w := by
  change SVec.toLinearMap (((adjunctionUnit J).app M).total w) = _
  simp only [adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ite_true, one_ne_zero, ite_false, add_zero, SVec.toLinearMap]

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

private theorem twist_equality {w v : A} (e : w = v) :
    twist k p (eqToHom e) = eqToHom e := by
  cases e
  exact twist_id (R := k) p w

/-- The actual unit column at a canonically identified output object. -/
def endpointUnitDotLinear (M : Superfunctor k C (SVec k)) (n : ℕ)
    (w : C) (v : A) (e : J.obj w = v) : M.obj w →ₗ[k] Obj J M.toFunctor v :=
  ((transformLinear hα M v) ^ n) ∘ₗ (postcompose J M.toFunctor (eqToHom e) ∘ₗ unit J M.toFunctor w)

theorem endpointUnitDotLinear_total (M : Superfunctor k C (SVec k)) (n : ℕ)
    (w : C) (v : A) (e : J.obj w = v) :
    postcompose J M.toFunctor (eqToHom e) ∘ₗ
      SVec.toLinearMap ((unitDotColumn J hα M n).total w) = endpointUnitDotLinear J hα M n w v e := by
  rw [unitDotColumn_total]
  have hn := transformLinear_naturality hα M (eqToHom e)
  rw [twist_equality] at hn
  have hp := intertwine_pow (postcompose J M.toFunctor (eqToHom e))
    (transformLinear hα M (J.obj w)) (transformLinear hα M v) hn.symm n
  unfold unitDotLinear endpointUnitDotLinear
  rw [← LinearMap.comp_assoc, hp, LinearMap.comp_assoc]

private theorem inducedMapIsoLinearEquiv_symm_hom
    {R S : Superfunctor k C (SVec k)} (e : R ≅ S)
    (he : e.inv ∈ parity (R := k) _ _ 0) (w : A) :
    (inducedMapIsoLinearEquiv J e w).symm.toLinearMap = mapComponent J e.inv 0 w := by
  have hp := IsSuperfunctor.map_mem (F := induction J) he
  have hz := Superfunctor.app_eq_zero_of_mem hp (by decide : (1 : ZMod 2) ≠ 0) w
  change ((induction J).map e.inv).total w = _
  rw [SuperNatTrans.total, hz, add_zero]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u

private theorem compose_intertwine
    {k V W Z : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (C₁ : V →ₗ[k] W) (C₂ : W →ₗ[k] Z)
    (f : Module.End k V) (g : Module.End k W) (h : Module.End k Z)
    (h₁ : C₁ ∘ₗ f = g ∘ₗ C₁) (h₂ : C₂ ∘ₗ g = h ∘ₗ C₂) :
    (C₂ ∘ₗ C₁) ∘ₗ f = h ∘ₗ (C₂ ∘ₗ C₁) := by
  apply LinearMap.ext
  intro x
  exact (congrArg C₂ (LinearMap.congr_fun h₁ x)).trans (LinearMap.congr_fun h₂ (C₁ x))

private theorem counit_source_iso
    {k V W Z P : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    [AddCommMonoid P] [Module k P]
    (e : V ≃ₗ[k] W) (C : W →ₗ[k] Z) (r : V →ₗ[k] P) (s : Z →ₗ[k] P)
    (A : W →ₗ[k] V) (B : V →ₗ[k] W)
    (hA : A = e.symm.toLinearMap) (hB : B = e.toLinearMap)
    (hc : s ∘ₗ C = r ∘ₗ A) : s ∘ₗ (C ∘ₗ B) = r := by
  rw [hA] at hc
  rw [hB]
  apply LinearMap.ext
  intro x
  exact (LinearMap.congr_fun hc (e x)).trans (congrArg r (e.symm_apply_apply x))

private theorem unit_power_square
    {k V W P : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid P] [Module k P]
    (C : V →ₗ[k] W) (f : Module.End k V) (g : Module.End k W)
    (u : P →ₗ[k] V) (v : P →ₗ[k] W)
    (hd : C ∘ₗ f = g ∘ₗ C) (hu : C ∘ₗ u = v) (n : ℕ) :
    C ∘ₗ ((f ^ n) ∘ₗ u) = (g ^ n) ∘ₗ v := by
  apply LinearMap.ext
  intro x
  exact (intertwine_pow_apply C f g (fun y => LinearMap.congr_fun hd y) n (u x)).trans
    (congrArg (fun y => (g ^ n) y) (LinearMap.congr_fun hu x))

private theorem cap_power_square
    {k V W P : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid P] [Module k P]
    (C : V →ₗ[k] W) (f : Module.End k V) (g : Module.End k W)
    (r : V →ₗ[k] P) (s : W →ₗ[k] P)
    (hd : C ∘ₗ f = g ∘ₗ C) (hc : s ∘ₗ C = r) (n : ℕ) :
    (s ∘ₗ (g ^ n)) ∘ₗ C = r ∘ₗ (f ^ n) := by
  apply LinearMap.ext
  intro x
  exact (congrArg s
    (intertwine_pow_apply C f g (fun y => LinearMap.congr_fun hd y) n x).symm).trans
      (LinearMap.congr_fun hc ((f ^ n) x))

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- The prescribed right-append dot in the literal truncated category. -/
theorem truncatedDot_supernatural : IsSupernatural k (D.parity i)
    (truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0)) :=
  truncatedAppendComponent_supernatural D Sc cutoff N (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The old column here is exactly the prescribed module-unit column. -/
theorem oldUnitColumn_eq (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    CyclotomicCrossingTensor.moduleUnitColumn D Sc cutoff i P n =
      BalancedInduction.unitDotColumn J (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) P n := rfl

/-- The old row here is exactly the prescribed module-cap row. -/
theorem oldCapRow_eq (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    CyclotomicCrossingTensor.moduleCapRow D Sc cutoff i P n =
      BalancedInduction.capDotRow J (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) P n := rfl

/-- The source comparison intertwines the given signed dot on every input
module map's parity-zero component, before restriction is specialized. -/
theorem weightedAppendSourceLinear_dot
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (c : R ⟶ weightedRestriction D Sc cutoff N L) (w : OldCategory D Sc cutoff) :
    weightedAppendSourceLinear D Sc cutoff N i R L c w ∘ₗ
        BalancedInduction.transformLinear
          (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) R w =
      BalancedInduction.transformLinear (truncatedDot_supernatural D Sc cutoff N i) L ((Q).obj w) ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i R L c w := by
  have h₁ := BalancedInduction.transform_mapComponent
    (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) R c 0 w
  have h₁' : BalancedInduction.mapComponent J c 0 w ∘ₗ
      BalancedInduction.transformLinear
          (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) R w =
      BalancedInduction.transformLinear
        (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i)
        (weightedRestriction D Sc cutoff N L) w ∘ₗ BalancedInduction.mapComponent J c 0 w := by
    simpa only [mul_zero, sign_zero, one_smul] using h₁.symm
  exact compose_intertwine (BalancedInduction.mapComponent J c 0 w)
    (weightedAppendComparisonLinear D Sc cutoff N i L w)
    (BalancedInduction.transformLinear
          (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) R w)
    (BalancedInduction.transformLinear
      (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) (weightedRestriction D Sc cutoff N L) w)
    (BalancedInduction.transformLinear (truncatedDot_supernatural D Sc cutoff N i) L ((Q).obj w)) h₁'
    (by simpa only [CyclotomicCrossingTensor.actualInductionDot] using
      appendWeightedModuleIso_hom_dot D Sc cutoff N i L w)

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The exact source chart of the mate comparison also transports the
ordinary counit, using the induced genuine restriction isomorphism. -/
theorem weightedMateSourceLinear_counit (w : OldCategory D Sc cutoff) :
    restrictionCounitLinear T M ((Q).obj w) ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
          ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).inv w =
      restrictionCounitLinear J RM w := by
  exact counit_source_iso
    (BalancedInduction.inducedMapIsoLinearEquiv J (weightedAppendRestrictionIso D Sc cutoff N i M).symm w)
    (weightedAppendComparisonLinear D Sc cutoff N i ((BalancedInduction.restriction T).obj M) w)
    (restrictionCounitLinear J RM w) (restrictionCounitLinear T M ((Q).obj w))
    (BalancedInduction.mapComponent J (weightedAppendRestrictionIso D Sc cutoff N i M).hom 0 w)
    (BalancedInduction.mapComponent J (weightedAppendRestrictionIso D Sc cutoff N i M).inv 0 w)
    (BalancedInduction.inducedMapIsoLinearEquiv_symm_hom J
      (weightedAppendRestrictionIso D Sc cutoff N i M).symm
      (weightedAppendRestrictionIso_hom_mem D Sc cutoff N i M) w).symm
    (BalancedInduction.inducedMapIsoLinearEquiv_hom J
      (weightedAppendRestrictionIso D Sc cutoff N i M).symm
      (weightedAppendRestrictionIso_inv_mem D Sc cutoff N i M) w).symm
    (appendWeightedModuleIso_hom_counit D Sc cutoff N i M w)

/-- The target chart transports the ordinary unit with its canonical output
object identity retained explicitly. -/
theorem weightedMateTargetLinear_unit (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) ∘ₗ
        BalancedInduction.unit J (RM).toFunctor w =
      BalancedInduction.postcompose T M.toFunctor
        (eqToHom (show (T).obj ((Q).obj w) = (Q).obj ((J).obj w) from rfl)) ∘ₗ
          BalancedInduction.unit T M.toFunctor ((Q).obj w) := by
  apply LinearMap.ext
  intro b
  have hu := appendWeightedModuleIso_hom_unit D Sc cutoff N i M w b
  have hp : BalancedInduction.postcompose T M.toFunctor
      (eqToHom (show (T).obj ((Q).obj w) = (Q).obj ((J).obj w) from rfl))
        (BalancedInduction.unit T M.toFunctor ((Q).obj w) b) =
      BalancedInduction.unit T M.toFunctor ((Q).obj w) b := by
    change BalancedInduction.postcompose T M.toFunctor (𝟙 ((Q).obj ((J).obj w))) _ = _
    exact LinearMap.congr_fun (BalancedInduction.postcompose_id T M.toFunctor ((Q).obj ((J).obj w))) _
  exact hu.trans hp.symm

/-- Every prescribed unscaled unit/dot column commutes with the selected
target chart, including either moving parity and arbitrary dot powers. -/
theorem weightedMateTargetLinear_unitDot (w : OldCategory D Sc cutoff) (n : ℕ) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) ∘ₗ
        BalancedInduction.unitDotLinear J
          (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) RM n w =
      BalancedInduction.endpointUnitDotLinear T (truncatedDot_supernatural D Sc cutoff N i) M n
        ((Q).obj w) ((Q).obj ((J).obj w)) rfl := by
  have h := unit_power_square
    (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w))
    (BalancedInduction.transformLinear
      (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) RM ((J).obj w))
    (BalancedInduction.transformLinear (truncatedDot_supernatural D Sc cutoff N i) M ((Q).obj ((J).obj w)))
    (BalancedInduction.unit J (RM).toFunctor w)
    (BalancedInduction.postcompose T M.toFunctor
      (eqToHom (show (T).obj ((Q).obj w) = (Q).obj ((J).obj w) from rfl)) ∘ₗ
        BalancedInduction.unit T M.toFunctor ((Q).obj w))
    (by simpa only [CyclotomicCrossingTensor.actualInductionDot] using
      appendWeightedModuleIso_hom_dot D Sc cutoff N i M ((J).obj w))
    (weightedMateTargetLinear_unit D Sc cutoff N i M w) n
  exact h

/-- Every prescribed unscaled dot/counit row commutes with the selected
source chart, with no row-normalization or comparison premise. -/
theorem weightedMateSourceLinear_capDot (w : OldCategory D Sc cutoff) (n : ℕ) :
    BalancedInduction.capDotLinear T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w) ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
          ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).inv w =
      BalancedInduction.capDotLinear J (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) RM n w := by
  exact cap_power_square
    (weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
      ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).inv w)
    (BalancedInduction.transformLinear (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i)
      ((BalancedInduction.restriction J).obj RM) w)
    (BalancedInduction.transformLinear (truncatedDot_supernatural D Sc cutoff N i)
      ((BalancedInduction.restriction T).obj M) ((Q).obj w))
    (restrictionCounitLinear J RM w) (restrictionCounitLinear T M ((Q).obj w))
    (weightedAppendSourceLinear_dot D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
      ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).inv w)
    (weightedMateSourceLinear_counit D Sc cutoff N i M w) n

end OddMath.QuiverHecke.ELVOld
