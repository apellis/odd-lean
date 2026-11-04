import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumPolynomialWindow
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms
noncomputable section
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
open ELVOld.PowerVacuumCoefficient ELVOld.ProbeVacuumCap
namespace NonVacuity.ELVTensorVacuumPolynomialWindow
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc' := parameterTwist D Sc
private abbrev sy := CyclotomicAction.AsymmetricParameters.symmetrizer
private theorem hc : Sc.Homogeneous := CyclotomicAction.AsymmetricParameters.homogeneous
private def m (_ : Bool) : ℕ := 2
private def cutoff (i : Bool) : ℕ := if i then 6 else 5
private def L (_ : Bool × ℕ) : ℕ := 4
private def ΛP : Bool → ℤ := fun i => probeCutoff D m i
private def ΛR : Bool → ℤ := fun i => cutoff i
private theorem hcP (i : Bool) : (probeCutoff D m i : ℤ) = D.h i ΛP := rfl
private theorem hcR (i : Bool) : (cutoff i : ℤ) = D.h i ΛR := rfl
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private theorem reservoir_positive (i : Bool) : 0 < cutoff i := by cases i <;> decide
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private abbrev W : ContentModules D Sc' cutoff bound 0 :=
  (restriction (contentInclusion D Sc' cutoff bound 0)).obj (weightedVacuum D Sc' cutoff L)
private abbrev H := VacuumTensor.probeFunctor D Sc' m cutoff bound W
private abbrev N₀ := probeOldVacuumRegular D Sc' m
private abbrev star : ContentCategory D Sc' cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨false, rfl⟩)

private theorem identity_total
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    (M : Superfunctor ℚ C (SVec ℚ)) (w : C) (z : M.obj w) :
    (𝟙 M : End M).total w z = z := by
  have h := congrArg SVec.toLinearMap (SuperNatTrans.id_total (R := ℚ) M.toFunctor w)
  exact LinearMap.congr_fun h z

private abbrev OddColour := {i : Bool // D.parity i = 1}
private def i₀ : OddColour := ⟨false, rfl⟩
private def i₁ : OddColour := ⟨true, rfl⟩

private theorem exterior_product_ne_zero :
    SKM.SYM.oddExteriorBasis D ℚ {i₀} * SKM.SYM.oddExteriorBasis D ℚ {i₁} ≠ 0 := by
  classical
  let : LinearOrder OddColour := WellOrderingRel.isWellOrder.linearOrder
  let ss := Set.powersetCard.ofCard (Finset.card_singleton i₀)
  let tt := Set.powersetCard.ofCard (Finset.card_singleton i₁)
  have hd : Disjoint ss.val tt.val := by
    change Disjoint ({i₀} : Finset OddColour) {i₁}
    simp only [Finset.disjoint_singleton]
    intro he
    have := congrArg Subtype.val he
    cases this
  have he := ExteriorAlgebra.basis_mul_of_disjoint
    (Finsupp.basisSingleOne : Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)) ss tt hd
  have hb := (Finsupp.basisSingleOne :
    Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)).ExteriorAlgebra.ne_zero
      (Set.powersetCard.disjUnion hd)
  intro hz
  change (Finsupp.basisSingleOne :
      Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)).ExteriorAlgebra ss *
    (Finsupp.basisSingleOne :
      Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)).ExteriorAlgebra tt = 0 at hz
  have hh := he.symm.trans hz
  rw [Units.smul_def] at hh
  exact hb ((Units.isUnit (Set.powersetCard.permOfDisjoint hd).sign).smul_eq_zero.mp hh)

private theorem source_product_ne_zero :
    SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁ ≠ 0 := by
  intro hz
  have he := congrArg (SKM.SYM.exteriorProjection D ℚ) hz
  simp only [map_mul, SKM.SYM.exteriorProjection_delta, map_zero] at he
  apply exterior_product_ne_zero
  simpa only [SKM.SYM.oddExteriorBasis_singleton] using he

private def deltaOne : AQ :=
  coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₁)
private theorem product_ne_zero : deltaClass * deltaOne ≠ 0 := by
  intro hz
  have hm : SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁ ∈
      SKM.SYM.CoefficientAtMost D ℚ 2 :=
    SKM.SYM.coefficientAtMost_mul D ℚ (m := 1) (n := 1)
      (x := SKM.SYM.delta D ℚ i₀) (y := SKM.SYM.delta D ℚ i₁)
      (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₀) (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₁)
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 2 4 (by decide) large powers_high
  have he := hi (a₁ := ⟨_, hm⟩) (a₂ := 0) (by
    change coefficientPowerQuotientMap D cutoff L _ = _
    rw [map_mul]
    exact hz.trans (map_zero _).symm)
  exact source_product_ne_zero (congrArg Subtype.val he)

example : deltaClass * deltaOne ≠ 0 := product_ne_zero

example (i : Bool) (M a : ℕ) (ha : a + 2 * M < cutoff i) :=
  tensorPolynomialCap_unit_window D Sc' m cutoff L i (reservoir_positive i) M a ha

private theorem top_column :
    tensorPolynomialClosure D Sc' m cutoff L false (reservoir_positive false) 2 0 =
      𝟙 (H.obj N₀) :=
  (tensorPolynomialCap_unit_window D Sc' m cutoff L false (reservoir_positive false) 2 0
    (by decide)).trans (ite_eq_left rfl)

example : tensorPolynomialClosure D Sc' m cutoff L true (reservoir_positive true) 2 0 = 0 :=
  (tensorPolynomialCap_unit_window D Sc' m cutoff L true (reservoir_positive true) 2 0
    (by decide)).trans (ite_eq_right (by decide))
example : tensorPolynomialClosure D Sc' m cutoff L true (reservoir_positive true) 2 1 =
    𝟙 (H.obj N₀) :=
  (tensorPolynomialCap_unit_window D Sc' m cutoff L true (reservoir_positive true) 2 1
    (by decide)).trans (ite_eq_left rfl)

private theorem tensor_product_ne_zero :
    tensorVacuumInputLinear D Sc' m cutoff L (deltaClass * deltaOne) ≠ 0 := by
  intro hz
  have he := tensorVacuumDecode_input D Sc' m cutoff L (deltaClass * deltaOne)
  rw [hz, map_zero] at he
  exact product_ne_zero he.symm

private theorem top_applies :
    (tensorPolynomialClosure D Sc' m cutoff L false (reservoir_positive false) 2 0).total star
      (tensorVacuumInputLinear D Sc' m cutoff L (deltaClass * deltaOne)) =
        tensorVacuumInputLinear D Sc' m cutoff L (deltaClass * deltaOne) := by
  rw [top_column]
  with_unfolding_all exact identity_total (H.obj N₀) star _

example : tensorPolynomialClosure D Sc' m cutoff L false (reservoir_positive false) 2 0 ≠ 0 := by
  intro hz
  have he := top_applies
  rw [hz] at he
  simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, SVec.zero_apply] at he
  exact tensor_product_ne_zero he.symm

example (a : AQ) :
    (tensorPolynomialClosure D Sc' m cutoff L false (reservoir_positive false) 2 0).total star
      (tensorVacuumInputLinear D Sc' m cutoff L (1 + a)) =
        tensorVacuumInputLinear D Sc' m cutoff L (1 + a) := by
  rw [top_column]
  with_unfolding_all exact identity_total (H.obj N₀) star _
end NonVacuity.ELVTensorVacuumPolynomialWindow
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumPolynomialWindow
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
