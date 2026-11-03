import OddMath.QuiverHecke.CyclotomicAction.ELVProbeLeftCapField
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeUnitCoefficientWindow
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldVacuumPolynomial

/-! # Native probe cap normalization

The last inverse-unit row in `SwappedVacuumNonpositiveBubbles.md`, §2,
extracts the prescribed native unit/dot column. The selected scalar charts
are cancelled, retaining the actual module unit, dot and coefficient cap.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u

private theorem inverseRow_window_cancel
    {k V W S T : Type u} [CommRing k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup S] [Module k S] [AddCommGroup T] [Module k T]
    (v : V ≃ₗ[k] W) (c : S →ₗ[k] T)
    (f : S →ₗ[k] V) (g : T →ₗ[k] W) (a : V →ₗ[k] S) (b : W →ₗ[k] T)
    (hf : v.toLinearMap ∘ₗ f = g ∘ₗ c)
    (ha : c ∘ₗ a = b ∘ₗ v.toLinearMap)
    (q : Prop) [Decidable q] (hg : g ∘ₗ b = if q then LinearMap.id else 0) :
    f ∘ₗ a = if q then LinearMap.id else 0 := by
  apply LinearMap.ext
  intro x
  apply v.injective
  have h : v (f (a x)) = (g ∘ₗ b) (v x) := by
    calc
      _ = g (c (a x)) := LinearMap.congr_fun hf (a x)
      _ = g (b (v x)) := congrArg g (LinearMap.congr_fun ha x)
      _ = _ := rfl
  rw [hg] at h
  by_cases hq : q
  · simpa only [hq, ↓reduceIte, LinearMap.id_apply, LinearMap.comp_apply] using h
  · simpa only [hq, ↓reduceIte, LinearMap.zero_apply, map_zero, LinearMap.comp_apply] using h

private theorem native_unitDot_window_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : C)
    (f : (restriction J).obj ((induction J).obj M) ⟶ M)
    (a : ℕ) (q : Prop) [Decidable q]
    (h : SVec.toLinearMap (f.total w) ∘ₗ
      SVec.toLinearMap ((unitDotColumn J hα M a).total w) =
      if q then LinearMap.id else 0) (b : M.obj w) :
    f.total w (SVec.toLinearMap (restrictedDotComponent J hα M w ^ a)
      (((adjunction J).unit.app M).total w b)) = if q then b else 0 := by
  have hp := LinearMap.congr_fun h b
  rw [unitDotColumn_total_restrictedDotComponent] at hp
  change f.total w (SVec.toLinearMap (restrictedDotComponent J hα M w ^ a)
    (((adjunction J).unit.app M).total w b)) =
    (if q then LinearMap.id else 0) b at hp
  by_cases hq : q
  · simpa only [hq, ↓reduceIte, LinearMap.id_apply] using hp
  · simpa only [hq, ↓reduceIte, LinearMap.zero_apply] using hp

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N) (i : I) (hi : i ∉ γ)
  (w : OldContentCategory D Sc (probeCutoff D m) γ)
local notation "cut" => probeCutoff D m
local notation "count" => contentUnitCount D cut i (γ : Multiset I)
local notation "K" => oldContentAppend D Sc cut γ i
include hN

/-- The actual native prescribed cap extracts its own given dotted-unit
column, with the canonical inverse-row unshift and no additional scalar. -/
theorem probeContentCoefficientCap_unitDot (r : Fin count) (a : ℕ) (ha : a < count) :
    SVec.toLinearMap ((contentCoefficientCap D Sc cut γ i N
      (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) ∘ₗ
      unitDotLinear K (probeOldContentAppendDot_supernatural D Sc m γ i) N a w =
    if a = r.val then LinearMap.id else 0 := by
  classical
  exact inverseRow_window_cancel
    (probeOutputValueLinearEquiv D Sc m γ N hN w)
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap _ _ _ _
    (probeMissingColourUnitCoefficient_cap D Sc m γ N hN i hi w r)
    (probeOutputFELinearEquiv_unitDot D Sc m γ N hN i w a) _
    (probeMissingColourUnitCoefficient_unitDot D Sc m γ N hN i hi w r a ha)

/-- The same native window on the component of the actual module
unit/dot column, rather than a separately specified coend operator. -/
theorem probeContentCoefficientCap_unitDotColumn
    (r : Fin count) (a : ℕ) (ha : a < count) :
    SVec.toLinearMap ((contentCoefficientCap D Sc cut γ i N
      (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) ∘ₗ
      SVec.toLinearMap ((unitDotColumn K
        (probeOldContentAppendDot_supernatural D Sc m γ i) N a).total w) =
    if a = r.val then LinearMap.id else 0 := by
  rw [unitDotColumn_total]
  exact probeContentCoefficientCap_unitDot D Sc m γ N hN i hi w r a ha

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []
local notation "s" => probeOldVacuumObject D Sc m

/-- The actual native dot on the same F/E probe superspace as the cap. -/
abbrev dot (i : I) : End ((source D Sc m i).obj s) :=
  restrictedDotComponent (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N s

/-- The given ordinary unit applied to the literal ground coordinate. -/
def unitVector (i : I) (c : k) : (source D Sc m i).obj s :=
  ((adjunction (K i)).unit.app N).total s ((probeVacuumScalarEquiv D Sc m) c)

/-- Native cap extraction on the actual dot-power/unit vectors, for every
scalar in the original regular empty probe. -/
theorem cap_dot_unit (i : I) (hP : 0 < cut i) (a : ℕ) (ha : a < cut i) (c : k) :
    (cap D Sc m i hP).total s (SVec.toLinearMap (dot D Sc m i ^ a) (unitVector D Sc m i c)) =
      if a + 1 = cut i then (probeVacuumScalarEquiv D Sc m) c else 0 := by
  let r : Fin (CyclotomicCrossingTensor.contentUnitCount D cut i (([] : List I) : Multiset I)) :=
    ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩
  have hac : a < CyclotomicCrossingTensor.contentUnitCount D cut i (([] : List I) : Multiset I) := by
    rw [VacuumCoefficient.count]
    exact ha
  have h := probeContentCoefficientCap_unitDotColumn D Sc m [] N
    (probeOldModule_evaluatesCoefficients D m Sc [] _) i (by simp) s r a hac
  have hp := native_unitDot_window_apply (K i)
    (probeOldContentAppendDot_supernatural D Sc m [] i) N s
    (cap D Sc m i hP) a (a = r.val) h ((probeVacuumScalarEquiv D Sc m) c)
  have har : a = r.val ↔ a + 1 = cut i := by dsimp only [r]; omega
  have he : (if a = r.val then (probeVacuumScalarEquiv D Sc m) c else 0) =
      if a + 1 = cut i then (probeVacuumScalarEquiv D Sc m) c else 0 := by
    by_cases hr : a = r.val
    · rw [ite_eq_left hr, ite_eq_left (har.mp hr)]
    · rw [ite_eq_right hr, ite_eq_right (fun htop => hr (har.mpr htop))]
  unfold dot unitVector
  convert hp.trans he using 1

/-- The native last row has the prescribed normalized ground window, with
no extra scalar and on every ground input. -/
theorem groundRow_dot_unit (i : I) (hP : 0 < cut i) (a : ℕ) (ha : a < cut i) (c : k) :
    groundRow D Sc m i hP (SVec.toLinearMap (dot D Sc m i ^ a) (unitVector D Sc m i c)) =
      if a + 1 = cut i then c else 0 := by
  change (probeVacuumScalarEquiv D Sc m).symm
    ((cap D Sc m i hP).total s (SVec.toLinearMap (dot D Sc m i ^ a) (unitVector D Sc m i c))) = _
  rw [cap_dot_unit D Sc m i hP a ha c]
  split_ifs <;> simp only [LinearEquiv.symm_apply_apply, map_zero]

/-- The actual native probe dot in this normalization obeys its signed
cyclotomic polynomial, in the endomorphism ring of the same superspace. -/
theorem dot_odd_polynomial (i : I) (hi : D.parity i = 1) :
    (dot D Sc m i ^ 2 + 1) ^ m i = 0 := by
  exact restrictedDotComponent_odd_probe_polynomial (K i)
    (probeOldContentAppendDot_supernatural D Sc m [] i) N s (m i)
    (probeOldVacuumModuleDot_odd D Sc m N
      (probeOldModule_evaluatesCoefficients D m Sc [] _) i hi)

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
