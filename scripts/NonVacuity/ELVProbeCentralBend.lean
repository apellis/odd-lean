import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCentralSlide
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath OddMath.QuiverHecke
open scoped TensorProduct
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor ELVOld.PowerVacuumCoefficient
open ELVOld.ProbeVacuumCap
namespace NonVacuity.ELVProbeCentralBend
private def tensorDetector {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (e : ℚ ≃ₗ[ℚ] V) : U ⊗[ℚ] V →ₗ[ℚ] U :=
  (TensorProduct.rid ℚ U).toLinearMap ∘ₗ TensorProduct.map LinearMap.id e.symm.toLinearMap
private theorem tensorDetector_tmul {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (e : ℚ ≃ₗ[ℚ] V) (u : U) :
    tensorDetector e (u ⊗ₜ[ℚ] e 1) = u := by
  simp only [tensorDetector, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.rid_tmul, one_smul]
private theorem module_id_ne_zero
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    (M : Superfunctor ℚ C (SVec ℚ)) (w : C) (z : M.obj w) (hz : z ≠ 0) : (𝟙 M : M ⟶ M) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : M ⟶ M => f.total w z) h
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    Superfunctor.zero_app, add_zero] at hh
  change z = 0 at hh
  exact hz hh
private theorem dots_different_of_opposite_window
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] {M Y : C}
    (u : M ⟶ Y) (v : Y ⟶ M) (x y : End Y) (n : ℕ)
    (hx : (u ≫ (x ^ n)) ≫ v = -(𝟙 M)) (hy : (u ≫ (y ^ n)) ≫ v = 𝟙 M)
    (hid : (𝟙 M : M ⟶ M) ≠ 0) : x ≠ y := by
  intro hxy
  rw [hxy, hy] at hx
  have htwo : (2 : ℚ) • (𝟙 M : M ⟶ M) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hx
  exact hid (((smul_eq_zero (R := ℚ)).mp htwo).resolve_left (by norm_num))

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private def cutoff (i : Bool) : ℕ := if i then 6 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private abbrev R₀ := contentModuleTarget D Sc cutoff bound (0 : Multiset Bool)
private abbrev W : ContentModules D Sc cutoff bound 0 :=
  (restriction (contentInclusion D Sc cutoff bound 0)).obj (weightedVacuum D Sc cutoff L)
private def H : modulePiCategory D Sc m ⟶ R₀ := VacuumTensor.probeFunctor D Sc m cutoff bound W
private abbrev N₀ := probeOldVacuumRegular D Sc m
private abbrev star : ContentCategory D Sc cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨false, rfl⟩)
private theorem delta_ne_zero : deltaClass ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by decide) large powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨false, rfl⟩⟩) (a₂ := 0)
    (by simpa only [deltaClass, ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨false, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)
private def occupied : (H.obj N₀).obj star :=
  (weightedEmptyEquiv D Sc cutoff L deltaClass) ⊗ₜ[ℚ] (probeVacuumScalarEquiv D Sc m 1)
private theorem occupied_ne_zero : occupied ≠ 0 := by
  intro hz
  have hh := congrArg (tensorDetector (U := W.obj star) (probeVacuumScalarEquiv D Sc m)) hz
  change tensorDetector (probeVacuumScalarEquiv D Sc m)
    (weightedEmptyEquiv D Sc cutoff L deltaClass ⊗ₜ[ℚ] probeVacuumScalarEquiv D Sc m 1) = 0 at hh
  rw [tensorDetector_tmul] at hh
  exact delta_ne_zero ((weightedEmptyEquiv D Sc cutoff L).injective
    (hh.trans (map_zero _).symm))

/-- This is the literal tensor vacuum H, occupied by a surviving exterior
coefficient; it is not a zero Hom object. -/
example : occupied ≠ 0 := occupied_ne_zero

/-- Both asymmetric odd probes have a nonzero raw dot distinct from the
unsigned coordinate dot on this SAME occupied tensor vacuum. -/
example (i : Bool) : shiftedPreDot D Sc m R₀ i H ≠ coordinatePreDotPower D Sc m R₀ i H 1 := by
  have ha : probeCutoff D m i - 1 < probeCutoff D m i := by have := positive i; omega
  have ht : probeCutoff D m i - 1 + 1 = probeCutoff D m i := by have := positive i; omega
  have hx := shiftedPreCap_rawDot_unit D Sc m R₀ i (positive i) H (probeCutoff D m i - 1) ha
  have hy := shiftedPreCap_dot_unit D Sc m R₀ i (positive i) H (probeCutoff D m i - 1) ha
  have hs : koszulSign (((probeCutoff D m i - 1 : ℕ) : ZMod 2) * D.parity i)
      ((probeCutoff D m i - 1) • D.parity i) = -1 := by cases i <;> rfl
  rw [ite_eq_left ht, hs, neg_one_zsmul] at hx
  rw [ite_eq_left ht, coordinatePreDotPower_eq] at hy
  exact dots_different_of_opposite_window _ _ _ _ _ hx hy
    (module_id_ne_zero (H.obj N₀) star occupied occupied_ne_zero)

/-- The actual kernel supplies the exponent for the finite A6 bend.
No nilpotence, extractor, or mate slide is assumed of this consumer. -/
example (i : Bool) : ∃ n : ℕ, 0 < n ∧
    evaluatedMixedBend D Sc m cutoff bound i (positive i) H =
      ∑ r ∈ Finset.range (2 * n), (-1 : ℤ) ^ r •
        ((Ring.inverse (shiftedPreDot D Sc m R₀ i H) ^ (r + 1)) ≫ shiftedPreCap D Sc m R₀ i (positive i) H ≫
          (adjunction (contentAppend D Sc cutoff bound (0 : Multiset Bool) [i])).unit.app (H.obj N₀) ≫
            (evaluatedPostDot D Sc m cutoff bound i H ^ r)) := by
  obtain ⟨n, hn, hy⟩ := diagonalPostDot_pow_zero D Sc m cutoff bound
    CyclotomicAction.AsymmetricParameters.symmetrizer CyclotomicAction.AsymmetricParameters.homogeneous i
  exact ⟨n, hn, evaluatedMixedBend_odd_expansion D Sc m cutoff bound i (by cases i <;> rfl) (positive i) H n (hy H)⟩

/-- The signed slide is a theorem of the exact evaluated bend, on both
occupied odd probes and the literal power quotient. -/
example (i : Bool) :
    evaluatedMixedBend D Sc m cutoff bound i (positive i) H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      koszulSign (D.parity i) (D.parity i) •
        (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i (positive i) H) =
      shiftedPreCap D Sc m R₀ i (positive i) H ≫
        (adjunction (contentAppend D Sc cutoff bound (0 : Multiset Bool) [i])).unit.app (H.obj N₀) :=
  evaluatedMixedBend_odd_slide D Sc m cutoff bound
    CyclotomicAction.AsymmetricParameters.symmetrizer CyclotomicAction.AsymmetricParameters.homogeneous
      i (by cases i <;> rfl) (positive i) H
end NonVacuity.ELVProbeCentralBend
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVProbeCentralBend,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCentralSlide] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module: {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
