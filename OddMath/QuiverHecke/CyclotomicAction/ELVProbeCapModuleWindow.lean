import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapWindow
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Module-map normalization of the regular probe cap

The normalized cap of `SwappedActionAssembly.md`, §5 (A14), must retain
its module maps before Hom precomposition. We promote the given inverse-row
window and signed dot polynomial to that level, without a left adjunction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem module_window
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M S : Superfunctor k C (SVec k)} (a : M ⟶ S) (b : S ⟶ M)
    (q : Prop) [Decidable q]
    (h : ∀ w, SVec.toLinearMap (b.total w) ∘ₗ SVec.toLinearMap (a.total w) =
      if q then LinearMap.id else 0) :
    a ≫ b = if q then 𝟙 M else 0 := by
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total]
  have hw := h w
  by_cases hq : q
  · rw [ite_eq_left hq] at hw ⊢
    apply LinearMap.ext
    intro x
    rw [SVec.comp_apply]
    have hid : (𝟙 M : M ⟶ M).total w = 𝟙 (M.obj w) := SuperNatTrans.id_total M.toFunctor w
    rw [hid, SVec.id_apply]
    simpa only [LinearMap.comp_apply, SVec.coe_toLinearMap, LinearMap.id_apply]
      using LinearMap.congr_fun hw x
  · rw [ite_eq_right hq] at hw ⊢
    apply LinearMap.ext
    intro x
    rw [SVec.comp_apply]
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, SVec.zero_apply, LinearMap.comp_apply, SVec.coe_toLinearMap, LinearMap.zero_apply]
      using LinearMap.congr_fun hw x

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The same dot used in the normalized ground window, retained as a
module endomorphism before evaluation or Hom precomposition. -/
abbrev moduleDot (i : I) : End (source D Sc m i) :=
  restrictedDotEnd (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N

/-- The given dotted-unit column followed by the prescribed last inverse
row is the Kronecker identity as a module map, at every empty-content object. -/
theorem unitDotColumn_cap (i : I) (hP : 0 < cut i) (a : ℕ) (ha : a < cut i) :
    unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a ≫
      cap D Sc m i hP = if a + 1 = cut i then 𝟙 N else 0 := by
  classical
  let r : Fin (contentUnitCount D cut i (([] : List I) : Multiset I)) :=
    ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩
  have hac : a < contentUnitCount D cut i (([] : List I) : Multiset I) := by
    rw [VacuumCoefficient.count]
    exact ha
  have h := module_window
    (unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a)
    (cap D Sc m i hP) (a = r.val) (fun w =>
      probeContentCoefficientCap_unitDotColumn D Sc m [] N
        (probeOldModule_evaluatesCoefficients D m Sc [] _) i (by simp) w r a hac)
  have har : a = r.val ↔ a + 1 = cut i := by dsimp only [r]; omega
  simpa only [har] using h

/-- The signed probe polynomial holds on the same module endomorphism
whose components were used for the normalized cap window. -/
theorem moduleDot_odd_polynomial (i : I) (hi : D.parity i = 1) :
    (moduleDot D Sc m i ^ 2 + 1) ^ m i = 0 := by
  exact additiveFunctor_odd_probe_polynomial (restriction (K i))
    (dotEnd (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N) (m i)
    (probeOldVacuumModuleDot_odd D Sc m N
      (probeOldModule_evaluatesCoefficients D m Sc [] _) i hi)

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
