import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerNonpositiveCap
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVCoefficientPowerNonpositiveCap
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (i : Bool) : ℕ := if i then 5 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
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

private theorem nonpositive_height (i : Bool) : 2 * 2 ≤ cutoff i := large i

example (i : Bool) :
    polynomialCapMoment D Sc cutoff L i (positive i) 2 (cutoff i - 2 * 2) =
      LinearMap.mulLeft ℚ ((-1 : ℚ) ^ (cutoff i + 1) • deltaClass i) :=
  polynomialCapMoment_nonpositive_first_odd D Sc cutoff L i rfl (positive i) 2 (nonpositive_height i)

private theorem first_false (z : AQ) :
    polynomialCapMoment D Sc cutoff L false (positive false) 2 0 z = -(deltaClass false * z) := by
  have h := LinearMap.congr_fun (polynomialCapMoment_nonpositive_first_odd D Sc cutoff L false rfl
    (positive false) 2 (nonpositive_height false)) z
  change polynomialCapMoment D Sc cutoff L false (positive false) 2 0 z =
    (((-1 : ℚ) ^ 5) • deltaClass false) * z at h
  rw [show (-1 : ℚ) ^ 5 = -1 by norm_num, smul_mul_assoc] at h
  exact h.trans (neg_one_smul ℚ (deltaClass false * z))

private theorem first_true (z : AQ) :
    polynomialCapMoment D Sc cutoff L true (positive true) 2 1 z = deltaClass true * z := by
  have h := LinearMap.congr_fun (polynomialCapMoment_nonpositive_first_odd D Sc cutoff L true rfl
    (positive true) 2 (nonpositive_height true)) z
  change polynomialCapMoment D Sc cutoff L true (positive true) 2 1 z =
    (((-1 : ℚ) ^ 6) • deltaClass true) * z at h
  rw [show (-1 : ℚ) ^ 6 = 1 by norm_num, one_smul] at h
  exact h

private theorem anti : deltaClass true * deltaClass false = -(deltaClass false * deltaClass true) := by
  change coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₁) *
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₀) = _
  rw [← map_mul, SKM.SYM.delta_anticommute, map_neg, map_mul]
  rfl

/-- Zero height at the even reservoir cutoff retains its minus sign. -/
example : polynomialCapMoment D Sc cutoff L false (positive false) 2 0
    (deltaClass true) = -(deltaClass false * deltaClass true) := first_false _

/-- Negative height at the odd reservoir cutoff retains its plus exterior normalization,
while the independently odd input still detects the left multiplication order. -/
example : polynomialCapMoment D Sc cutoff L true (positive true) 2 1
    (deltaClass false) = -(deltaClass false * deltaClass true) := by
  rw [first_true, anti]

example : polynomialCapMoment D Sc cutoff L true (positive true) 2 1
    (deltaClass false) ≠ 0 := by
  rw [first_true, anti, neg_ne_zero]
  exact product_ne_zero

example : polynomialCapMoment D Sc cutoff L true (positive true) 2 1
    (1 + deltaClass false) = deltaClass true - deltaClass false * deltaClass true := by
  rw [first_true, mul_add, mul_one, anti, sub_eq_add_neg]

end NonVacuity.ELVCoefficientPowerNonpositiveCap

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerNonpositiveCap
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
