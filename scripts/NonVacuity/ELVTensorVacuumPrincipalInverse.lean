import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumPrincipalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
open ELVOld.PowerVacuumCoefficient ELVOld.ProbeVacuumCap ELVOld.WeightTensorVacuum
namespace NonVacuity.ELVTensorVacuumPrincipalInverse
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc' := parameterTwist D Sc
private abbrev sy := CyclotomicAction.AsymmetricParameters.symmetrizer
private theorem hc : Sc.Homogeneous := CyclotomicAction.AsymmetricParameters.homogeneous
private def m (_ : Bool) : ℕ := 2
private def cutoff (_ : Bool) : ℕ := 4
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
private abbrev bound := PowerWordContent.powerBound D cutoff L
private abbrev W : ContentModules D Sc' cutoff bound 0 :=
  (restriction (contentInclusion D Sc' cutoff bound 0)).obj (weightedVacuum D Sc' cutoff L)
private abbrev H := VacuumTensor.probeFunctor D Sc' m cutoff bound W
private abbrev N₀ := probeOldVacuumRegular D Sc' m
private abbrev star : ContentCategory D Sc' cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨false, rfl⟩)

example := tensorOutputAt_empty D Sc' m cutoff L ΛR
example := tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hcP hcR
example (i : Bool) := tensorVacuumPrincipalFactorIso_hom D Sc m cutoff L ΛP ΛR hcP hcR
  sy hc i (by cases i <;> rfl)
example (i : Bool) := tensorPaddedPrincipal_isIso D Sc m cutoff L ΛP ΛR hcP hcR
  sy hc i (by cases i <;> rfl)
example (i : Bool) := tensorVacuumPrincipalBend_isIso D Sc m cutoff L ΛP ΛR hcP hcR
  sy hc i rfl (positive i) rfl
example (i : Bool) := tensorVacuumPrincipalCap_eq_polynomial D Sc m cutoff L ΛP ΛR hcP hcR
  sy hc i rfl (positive i) (reservoir_positive i) rfl
example (i : Bool) (z : (H.obj N₀).obj star) :=
  tensorVacuumPrincipalClosure_decode D Sc m cutoff L ΛP ΛR hcP hcR sy hc i
    rfl (positive i) (reservoir_positive i) rfl z

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

private theorem decoded_product : tensorVacuumDecodeLinear D Sc' m cutoff L
    ((tensorVacuumPrincipalClosure D Sc m cutoff L ΛP ΛR hcP hcR sy hc false rfl
      (positive false) rfl).total star (tensorVacuumInputLinear D Sc' m cutoff L deltaOne)) =
      -(deltaClass * deltaOne) := by
  rw [tensorVacuumPrincipalClosure_decode D Sc m cutoff L ΛP ΛR hcP hcR sy hc false rfl
    (positive false) (reservoir_positive false) rfl, tensorVacuumDecode_input]
  change -deltaClass * deltaOne = _
  exact neg_mul _ _

example : (tensorVacuumPrincipalClosure D Sc m cutoff L ΛP ΛR hcP hcR sy hc false rfl
    (positive false) rfl).total star (tensorVacuumInputLinear D Sc' m cutoff L deltaOne) ≠ 0 := by
  intro hz
  have he := decoded_product
  rw [hz, map_zero] at he
  exact (neg_ne_zero.mpr product_ne_zero) he.symm

example : tensorVacuumDecodeLinear D Sc' m cutoff L
    ((tensorVacuumPrincipalClosure D Sc m cutoff L ΛP ΛR hcP hcR sy hc false rfl
      (positive false) rfl).total star (tensorVacuumInputLinear D Sc' m cutoff L (1 + deltaOne))) =
      -deltaClass - deltaClass * deltaOne := by
  rw [tensorVacuumPrincipalClosure_decode D Sc m cutoff L ΛP ΛR hcP hcR sy hc false rfl
    (positive false) (reservoir_positive false) rfl, tensorVacuumDecode_input]
  change -deltaClass * (1 + deltaOne) = _
  noncomm_ring
end NonVacuity.ELVTensorVacuumPrincipalInverse
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumWholeInput,
      `OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumPrincipalFactor,
      `OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumPrincipalInverse] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module: {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
