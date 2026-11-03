import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientModuleMaps
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVCoefficientModuleMaps
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

private def deltaCoefficient (i : Bool) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private theorem delta_odd (i : Bool) : deltaCoefficient i ∈ SKM.SYM.elvCoefficientParity D cutoff 1 :=
by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.coefficientBasis_mem_parity D ℚ (0, {⟨i, rfl⟩}))
  change SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨i, rfl⟩) ∈
    SKM.SYM.elvCoefficientParity D cutoff 1
  simpa only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, Finset.card_singleton, Nat.cast_one,
    ← SKM.SYM.delta_eq_coefficientBasis] using h
private abbrev M := coefficientPowerVacuum D Sc cutoff L
private abbrev E := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
private abbrev empty : OldCategory D Sc cutoff := ⟨[]⟩
private def phi (i : Bool) : End M := vacuumCoefficientAction D Sc cutoff L (deltaClass i)
private theorem phi_eq (i : Bool) : phi i = coefficientModuleAction D Sc cutoff M (deltaCoefficient i) := rfl

example (i : Bool) : phi i ∈ parity (R := ℚ) M M 1 := by
  rw [phi_eq]
  exact coefficientModuleAction_mem D Sc cutoff M (delta_odd i)

example (a b : AQ) : vacuumCoefficientAction D Sc cutoff L (a * b) =
    vacuumCoefficientAction D Sc cutoff L a * vacuumCoefficientAction D Sc cutoff L b :=
  map_mul _ a b

example (a z : AQ) : (vacuumCoefficientAction D Sc cutoff L a).total empty (E z) = E (a * z) :=
  vacuumCoefficientAction_empty D Sc cutoff L a z

example : (phi false).total empty (E (deltaClass true)) ≠ 0 := by
  rw [phi, vacuumCoefficientAction_empty]
  exact fun hz => product_ne_zero (E.injective (hz.trans E.map_zero.symm))

example : (vacuumCoefficientAction D Sc cutoff L (1 + deltaClass false)).total empty
    (E (1 + deltaClass true)) = E (1 + deltaClass true + deltaClass false +
      deltaClass false * deltaClass true) := by
  rw [vacuumCoefficientAction_empty]
  congr 1
  noncomm_ring

private abbrev J := append D Sc cutoff false
private abbrev w : OldCategory D Sc cutoff := J.obj empty
private def oddKernel : J.obj empty ⟶ w :=
  J.map (X := empty) (Y := empty) (coefficientEndomorphism D Sc cutoff [] (deltaCoefficient true))
private theorem oddKernel_odd : oddKernel ∈ parity (R := ℚ) (J.obj empty) w 1 :=
  IsSuperfunctor.map_mem (F := J) (coefficientEndomorphism_mem D Sc cutoff [] (delta_odd true))
private def input := BalancedInduction.tensor J M.toFunctor empty oddKernel (E 1)

/-- A genuine odd source-module map twists an independently odd tensor kernel. -/
example : ((BalancedInduction.induction J).map (phi false)).total w input =
    BalancedInduction.tensor J M.toFunctor empty (twist ℚ 1 oddKernel) (E (deltaClass false)) := by
  rw [phi_eq]
  have h := coefficientModuleAction_induction_tensor D Sc cutoff J M (delta_odd false)
    empty w oddKernel (E 1)
  change ((BalancedInduction.induction J).map
    (coefficientModuleAction D Sc cutoff M (deltaCoefficient false))).total w input = _ at h
  rw [PowerVacuumCoefficient.empty_coefficient_action, mul_one] at h
  exact h

end NonVacuity.ELVCoefficientModuleMaps

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientModuleMaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
