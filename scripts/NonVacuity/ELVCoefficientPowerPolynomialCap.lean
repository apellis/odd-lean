import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerPolynomialCap
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVCoefficientPowerPolynomialCap
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (i : Bool) : ℕ := if i then 6 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private def probePower (i : Bool) : ℕ := if i then 3 else 2
private theorem zero_height (i : Bool) : cutoff i = 2 * probePower i := by cases i <;> decide
private theorem positive (i : Bool) : 0 < cutoff i := by cases i <;> decide
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private def elementaryClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.e D ℚ i 0)

private theorem window_ne_zero {d : ℕ} (hd : d < 4) (a : SKM.SYM D ℚ)
    (ha : a ∈ SKM.SYM.CoefficientAtMost D ℚ d) (h0 : a ≠ 0) :
    coefficientPowerQuotientMap D cutoff L a ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L d 4 hd large powers_high
  have he := hi (a₁ := ⟨a, ha⟩) (a₂ := 0)
    (by simpa only [ZeroMemClass.coe_zero, map_zero] using hz)
  exact h0 (congrArg Subtype.val he)

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

private theorem product_ne_zero : deltaClass false * deltaClass true ≠ 0 := by
  change coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₀) *
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₁) ≠ 0
  rw [← map_mul]
  have hm : SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁ ∈
      SKM.SYM.CoefficientAtMost D ℚ 2 :=
    SKM.SYM.coefficientAtMost_mul D ℚ (m := 1) (n := 1)
      (x := SKM.SYM.delta D ℚ i₀) (y := SKM.SYM.delta D ℚ i₁)
      (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₀) (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₁)
  exact window_ne_zero (by decide : 2 < 4) _ hm source_product_ne_zero

/-- The actual polynomial-cap closures act by minus the left exterior coefficient,
on the entire literal quotient, at zero height. -/
example (i : Bool) :
    polynomialCapMoment D Sc cutoff L i (positive i) (probePower i) 0 =
      LinearMap.mulLeft ℚ (-deltaClass i) :=
  polynomialCapMoment_zero_height_odd D Sc cutoff L i rfl (positive i) (probePower i) (zero_height i)

private theorem closure_false (z : AQ) :
    polynomialCapMoment D Sc cutoff L false (positive false) (probePower false) 0 z =
      -(deltaClass false * z) := by
  have h := LinearMap.congr_fun (polynomialCapMoment_zero_height_odd D Sc cutoff L false rfl
    (positive false) (probePower false) (zero_height false)) z
  change polynomialCapMoment D Sc cutoff L false (positive false) (probePower false) 0 z =
    (-deltaClass false) * z at h
  exact h.trans (neg_mul _ _)

private theorem anti : deltaClass true * deltaClass false = -(deltaClass false * deltaClass true) := by
  change coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₁) *
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₀) = _
  rw [← map_mul, SKM.SYM.delta_anticommute, map_neg, map_mul]
  rfl

/-- An independently odd input fixes the original left coefficient order,
and its image in the actual quotient is proved nonzero. -/
example : polynomialCapMoment D Sc cutoff L false (positive false) (probePower false) 0
    (deltaClass true) = -(deltaClass false * deltaClass true) := closure_false _

example : polynomialCapMoment D Sc cutoff L false (positive false) (probePower false) 0
    (deltaClass true) ≠ 0 := by
  rw [closure_false, neg_ne_zero]
  exact product_ne_zero

example : polynomialCapMoment D Sc cutoff L true (positive true) (probePower true) 0
    (deltaClass false) = deltaClass false * deltaClass true := by
  have h := LinearMap.congr_fun (polynomialCapMoment_zero_height_odd D Sc cutoff L true rfl
    (positive true) (probePower true) (zero_height true)) (deltaClass false)
  change polynomialCapMoment D Sc cutoff L true (positive true) (probePower true) 0
    (deltaClass false) = (-deltaClass true) * deltaClass false at h
  rw [neg_mul, anti, neg_neg] at h
  exact h

example : polynomialCapMoment D Sc cutoff L false (positive false) (probePower false) 0
    (1 + deltaClass true) = -deltaClass false - deltaClass false * deltaClass true := by
  rw [closure_false]
  noncomm_ring

end NonVacuity.ELVCoefficientPowerPolynomialCap

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerPolynomialCap
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
