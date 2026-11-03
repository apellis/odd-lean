import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVWeightedPowerCoefficients
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private abbrev W := weightedVacuum D Sc cutoff L
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private abbrev T (i : Bool) := truncatedAppend D Sc cutoff bound [i]
private abbrev s := (oldTruncateFunctor D Sc cutoff bound).obj (⟨[]⟩ : OldCategory D Sc cutoff)
private abbrev V (i : Bool) := ((restriction (T i)).obj ((induction (T i)).obj W)).obj s
private def deltaA (j : Bool) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨j, rfl⟩)
private def deltaClass (j : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨j, rfl⟩)
private def outputCoefficient (i j : Bool) (z : V i) : V i :=
  ((restriction (T i)).obj ((induction (T i)).obj W)).map
    (weightedCoefficientEnd D Sc cutoff L (deltaA j)) z
private def topVector (i : Bool) (a : AQ) : V i :=
  (unitDotColumn (T i) (truncatedDot_supernatural D Sc cutoff bound i) W 3).total s
    (weightedEmptyEquiv D Sc cutoff L a)
private theorem degree (i : Bool) : (cutoff i - 1) • D.parity i = (1 : ZMod 2) := by
  cases i <;> decide
private theorem deltaA_mem (j : Bool) : deltaA j ∈ SKM.SYM.elvCoefficientParity D cutoff 1 := by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.polynomialExterior_delta_mem_odd D (k := ℚ) ⟨j, rfl⟩)
  simpa only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, deltaA] using h
private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
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


private theorem quotient_product_ne_zero : deltaClass false * deltaClass true ≠ 0 := by
  have hm := SKM.SYM.coefficientAtMost_mul D ℚ
    (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₀)
    (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₁)
  intro hz
  have he : coefficientPowerQuotientMap D cutoff L
      (SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁) = 0 := by
    simpa only [map_mul, deltaClass, i₀, i₁] using hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 2 4 (by decide)
    (fun _ => by rfl) powers_high
  have hh := hi (a₁ := ⟨_, hm⟩) (a₂ := 0) he
  exact source_product_ne_zero (congrArg Subtype.val hh)

/-- The actual weighted inverse row has its nonzero odd-coefficient sign
on the prescribed top dotted unit, with the original left product order. -/
private theorem weighted_odd_extract (i j k : Bool) :
    weightedFunctional D Sc cutoff L i (by norm_num [cutoff])
      (outputCoefficient i j (topVector i (deltaClass k))) = -(deltaClass j * deltaClass k) := by
  have h := weightedFunctional_coefficient D Sc cutoff L i (by norm_num [cutoff]) (deltaA_mem j)
    (topVector i (deltaClass k))
  have hw := weightedFunctional_unitDotColumn D Sc cutoff L i (by norm_num [cutoff])
    3 (by norm_num [cutoff]) (deltaClass k)
  change weightedFunctional D Sc cutoff L i (by norm_num [cutoff])
      (outputCoefficient i j (topVector i (deltaClass k))) =
    koszulSign ((cutoff i - 1) • D.parity i) 1 •
      (deltaClass j * weightedFunctional D Sc cutoff L i (by norm_num [cutoff])
        (topVector i (deltaClass k))) at h
  change weightedFunctional D Sc cutoff L i (by norm_num [cutoff])
    (topVector i (deltaClass k)) = deltaClass k at hw
  simpa only [degree, koszulSign_one_one, neg_one_zsmul, hw] using h

example (i : Bool) : weightedFunctional D Sc cutoff L i (by norm_num [cutoff])
    (outputCoefficient i false (topVector i (deltaClass true))) ≠ 0 := by
  rw [weighted_odd_extract]
  exact neg_ne_zero.mpr quotient_product_ne_zero

private theorem anticommute : deltaClass false * deltaClass true = -(deltaClass true * deltaClass false) := by
  change coefficientPowerQuotientMap D cutoff L _ * coefficientPowerQuotientMap D cutoff L _ = -(_ * _)
  rw [← map_mul, SKM.SYM.delta_anticommute, map_neg, map_mul]
  rfl

/-- Exchanging the two occupied odd colours reverses the extracted sign;
the actual weighted cap sees their independent product. -/
example (i : Bool) :
    weightedFunctional D Sc cutoff L i (by norm_num [cutoff])
        (outputCoefficient i false (topVector i (deltaClass true))) =
      -(weightedFunctional D Sc cutoff L i (by norm_num [cutoff])
        (outputCoefficient i true (topVector i (deltaClass false)))) := by
  rw [weighted_odd_extract, weighted_odd_extract]
  exact congrArg Neg.neg anticommute
end NonVacuity.ELVWeightedPowerCoefficients
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
